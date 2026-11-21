#!/usr/bin/env python3
"""Run the duplicate search and the statement index on a built Lake project, and summarize them.

    dupsearch.py search PROJECT --root MOD [--root MOD …] [--exclude MOD …] [--only FILE]
                        [--shards N] [--jobs J] [--heartbeats K] [--depth D] --out DIR
    dupsearch.py index PROJECT --root MOD [--root MOD …] [--exclude MOD …] --out DIR
    dupsearch.py summarize DIR

PROJECT is the directory of the project's lakefile, with the library already built
(`lake build`). The library is the modules under each root `R`: the sources `R.lean` and
`R/**/*.lean` (a library need not have a root file). The Lean side of the tool (`DupSearch/`) is
compiled into DIR with the project's own toolchain and put on the search path through
`LEAN_PATH`, so the project needs no change and no dependency on this package.

Both commands first scan the compiled library (`DupSearch/Modules.lean`) for constants that two
modules declare incompatibly. Such modules cannot be imported together, so the library is split
among as few environments as the clashes allow, each importing as much of the library as it can,
and every module's theorems are handled in exactly one of them. The clashes are reported.

DIR receives the records as JSON lines (`scan.jsonl`, `search-eE-K.jsonl`, `index-eE.jsonl`; see
the module docs of `DupSearch/`), `environments.json`, and `run-search.json` or `run-index.json`
recording the project's commit, its toolchain and the command. `summarize` writes `summary.json`
and `summary.md` from whatever records DIR holds.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

TOOL = Path(__file__).resolve().parent
TOOL_MODULES = ["DupSearch.Basic", "DupSearch.Modules", "DupSearch.Index", "DupSearch.Normalize",
                "DupSearch.Shape", "DupSearch.Relevance", "DupSearch.Search"]
# The default relevance threshold and budget of the candidates tried again at default
# transparency (`DupSearch/Search.lean`), calibrated on a full run of a large library (README).
RELEVANCE = 0.3
RELEVANT_HEARTBEATS = 20000
# The cheap search (--heuristic), from the coverage of every duplicate found on that run (README).
HEURISTIC = {"gate_top": 10, "own_proof": True, "definitional_heartbeats": 2000}
# Without --heuristic, the exhaustive search.
EXHAUSTIVE = {"gate_top": 0, "own_proof": False, "definitional_heartbeats": 0}
MODULE_NAME = re.compile(r"^[^\W\d][\w']*(\.[^\W\d][\w']*)*$")
# Modules whose lemmas make a hit "trivial": the statement holds by a fact of the language or its
# standard library rather than by a theorem anyone would restate.
CORE_ROOTS = {"Init", "Lean", "Std", "Batteries"}

Module = tuple[str, ...]  # a module name as its components


class Failure(Exception):
    """A run that cannot go on; the message says why."""


def dotted(m: Module) -> str:
    return ".".join(m)


def quoted(m: Module) -> str:
    """A module name as an `import` takes it, every component quoted: Lean accepts `«…»` on any
    component, and it keeps names such as `NoetherianGraded-00K2` importable."""
    return ".".join(f"«{c}»" for c in m)


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None) -> str:
    """Run a command and return its standard output; fail with its output when it fails."""
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    if proc.returncode != 0:
        raise Failure(f"{' '.join(cmd)} (in {cwd}) exited with {proc.returncode}:\n"
                      f"{proc.stdout}{proc.stderr}")
    return proc.stdout


def lean_string(s: str) -> str:
    """A Lean string literal for a path the driver chose; refuse anything needing escapes."""
    if any(c in s for c in '"\\') or any(ord(c) < 0x20 for c in s):
        raise Failure(f"path {s!r} contains a quote, a backslash or a control character")
    return f'"{s}"'


def check_project(project: Path) -> None:
    if not (project / "lean-toolchain").is_file():
        raise Failure(f"{project} has no lean-toolchain")
    if not any((project / f).is_file() for f in ("lakefile.toml", "lakefile.lean")):
        raise Failure(f"{project} has no lakefile")


def check_modules(names: list[str], what: str) -> None:
    for name in names:
        if not MODULE_NAME.match(name):
            raise Failure(f"{what} {name!r} is not a module name")


def library_modules(project: Path, roots: list[str]) -> list[Module]:
    """The modules of the library, sorted: the sources `R.lean` and `R/**/*.lean` of each root
    `R`, each of which must be built."""
    build = project / ".lake" / "build" / "lib" / "lean"
    modules, missing = set(), []
    for root in roots:
        base = project / Path(*root.split("."))
        sources = ([base.with_suffix(".lean")] if base.with_suffix(".lean").is_file() else []) + \
            (sorted(base.rglob("*.lean")) if base.is_dir() else [])
        if not sources:
            raise Failure(f"root {root}: no {base.with_suffix('.lean')} and no {base}/")
        for src in sources:
            rel = src.relative_to(project).with_suffix("")
            if any(c in part for part in rel.parts for c in "«»"):
                raise Failure(f"{src}: a module name component contains « or »")
            if not (build / rel).with_suffix(".olean").is_file():
                missing.append(".".join(rel.parts))
            modules.add(tuple(rel.parts))
    if missing:
        raise Failure(f"{len(missing)} modules are not built (run `lake build`), e.g. "
                      + ", ".join(missing[:10]))
    return sorted(modules)


def prepare_out(out: Path) -> None:
    """Create the output directory; refuse one that already holds records, so that two runs are
    never mixed."""
    if out.exists() and any(out.glob("*.jsonl")):
        raise Failure(f"{out} already holds records; give a fresh directory")
    out.mkdir(parents=True, exist_ok=True)


def tool_env(lib: Path) -> dict[str, str]:
    """The environment in which `lake env` finds the compiled tool: Lake appends an existing
    `LEAN_PATH` to its own."""
    env = dict(os.environ)
    env["LEAN_PATH"] = str(lib) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    return env


def compile_tool(project: Path, lib: Path) -> None:
    """Compile the tool's modules with the project's toolchain into `lib`."""
    env = tool_env(lib)
    for module in TOOL_MODULES:
        rel = Path(*module.split("."))
        olean = lib / rel.with_suffix(".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        run(["lake", "env", "lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
             "-R", str(TOOL), "-o", str(olean),
             "-i", str(olean.with_suffix(".ilean")), str(TOOL / rel.with_suffix(".lean"))],
            cwd=project, env=env)


def git_state(path: Path) -> dict[str, object]:
    """The commit of a checkout and whether it has uncommitted changes."""
    try:
        head = run(["git", "rev-parse", "HEAD"], cwd=path).strip()
        dirty = bool(run(["git", "status", "--porcelain", "--untracked-files=no"],
                         cwd=path).strip())
        return {"commit": head, "dirty": dirty}
    except (Failure, FileNotFoundError):
        return {"commit": None, "dirty": None}


def read_records(path: Path) -> list[dict]:
    if not path.is_file():
        return []
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def launch(project: Path, lib: Path, out: Path, stem: str, module: str, entry: str,
           imports: list[Module], config: dict) -> str:
    """Write a configuration and an entry file importing `imports` and calling `entry` of the
    tool's `module`, run the entry file, and return `stem` once the output ends in a `done`
    record."""
    config_path = out / f"{stem}.config.json"
    config_path.write_text(json.dumps(config, indent=2) + "\n")
    lean_path = out / f"{stem}.lean"
    header = "".join(f"import {m}\n" for m in [module, *map(quoted, imports)])
    lean_path.write_text(f"{header}\n#eval DupSearch.{entry} {lean_string(str(config_path))}\n")
    with open(out / f"{stem}.log", "w") as log:
        proc = subprocess.run(["lake", "env", "lean", str(lean_path)], cwd=project,
                              env=tool_env(lib), stdout=log, stderr=subprocess.STDOUT)
    records = read_records(Path(config["output"]))
    if proc.returncode != 0 or not records or records[-1].get("record") != "done":
        raise Failure(f"{stem} did not finish (exit {proc.returncode}); see {out / stem}.log")
    return stem


def launch_all(jobs: int, tasks: list[tuple]) -> None:
    """Run `launch` on each argument tuple, `jobs` at a time; fail with every failure."""
    failures = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [pool.submit(launch, *t) for t in tasks]
        for f in concurrent.futures.as_completed(futures):
            try:
                print(f"{f.result()} done", file=sys.stderr)
            except Failure as e:
                failures.append(str(e))
    if failures:
        raise Failure("\n".join(failures))


def base_config(args: argparse.Namespace, output: Path, modules: list[Module]) -> dict:
    return {"roots": args.root, "exclude": args.exclude, "output": str(output),
            "heartbeats": 0, "candidateHeartbeats": 0, "star": False, "libraryStar": False,
            "relevantStar": False, "relevance": 2.0, "relevantHeartbeats": 0,
            "gateTop": 0, "ownProof": False, "definitionalHeartbeats": 0,
            "normalizeHeartbeats": args.normalize_heartbeats,
            "transparency": "instances", "depth": 0,
            "shard": 0, "shards": 1, "only": None,
            "modules": [list(m) for m in modules]}


def closures(order: list[Module], imports: dict[Module, list[Module]]) -> dict[Module, int]:
    """The import closure of every module, itself included, as a bit set over `order`. The scan
    lists modules after their imports, so one pass suffices."""
    index = {m: i for i, m in enumerate(order)}
    cl: dict[Module, int] = {}
    for m in order:
        bits = 1 << index[m]
        for i in imports[m]:
            bits |= cl[i]
        cl[m] = bits
    return cl


def plan_environments(library: list[Module], order: list[Module],
                      imports: dict[Module, list[Module]],
                      clashes: list[tuple[Module, Module]]) -> list[dict]:
    """Split the library among environments that can each be imported: no environment holds both
    modules of a clash. Each module is assigned to the first environment its import closure fits
    in, then every environment takes in each further library module that fits, so that its
    search sees as many lemmas as the clashes allow."""
    index = {m: i for i, m in enumerate(order)}
    cl = closures(order, imports)
    pairs = [(1 << index[a], 1 << index[b]) for a, b in clashes]
    fits = lambda bits: not any(bits & a and bits & b for a, b in pairs)
    envs: list[dict] = []
    for m in library:
        if not fits(cl[m]):
            raise Failure(f"{dotted(m)} cannot be imported: its own imports clash")
        for env in envs:
            if fits(env["bits"] | cl[m]):
                env["bits"] |= cl[m]
                env["assigned"].append(m)
                break
        else:
            envs.append({"bits": cl[m], "assigned": [m]})
    for env in envs:
        env["imports"] = []
        for m in library:
            if fits(env["bits"] | cl[m]):
                env["bits"] |= cl[m]
                env["imports"].append(m)
    return [{"assigned": e["assigned"], "imports": e["imports"]} for e in envs]


def prepare(args: argparse.Namespace) -> dict:
    """Everything both commands do before their own work: check the arguments, find the library,
    compile the tool, scan the library and plan its environments."""
    project, out = Path(args.project).resolve(), Path(args.out).resolve()
    check_project(project)
    check_modules(args.root, "root")
    check_modules(args.exclude, "excluded module")
    library = library_modules(project, args.root)
    prepare_out(out)
    lib = out / "lib"
    compile_tool(project, lib)
    launch(project, lib, out, "scan", "DupSearch.Modules", "runScan", [],
           base_config(args, out / "scan.jsonl", library))
    records = read_records(out / "scan.jsonl")
    order = [tuple(r["parts"]) for r in records if r["record"] == "module"]
    imports = {tuple(r["parts"]): [tuple(i) for i in r["imports"]]
               for r in records if r["record"] == "module"}
    clashes = [(tuple(r["modules"][0]), tuple(r["modules"][1]))
               for r in records if r["record"] == "clash"]
    envs = plan_environments(library, order, imports, clashes)
    (out / "environments.json").write_text(json.dumps(
        [{"assigned": [dotted(m) for m in e["assigned"]],
          "imports": [dotted(m) for m in e["imports"]]} for e in envs], indent=2) + "\n")
    info = {
        "command": sys.argv,
        "project": str(project),
        "toolchain": (project / "lean-toolchain").read_text().strip(),
        "lean_version": run(["lake", "env", "lean", "--version"], cwd=project).strip(),
        "project_git": git_state(project),
        "tool_git": git_state(TOOL),
        "roots": args.root,
        "exclude": args.exclude,
        "library_modules": len(library),
        "clashes": len(clashes),
        "environments": len(envs),
        "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }
    (out / f"run-{args.command}.json").write_text(json.dumps(info, indent=2) + "\n")
    print(f"{len(library)} library modules, {len(clashes)} clashes, {len(envs)} environments",
          file=sys.stderr)
    return {"project": project, "out": out, "lib": lib, "library": library, "envs": envs}


def cmd_search(args: argparse.Namespace) -> None:
    if args.shards < 1 or args.jobs < 1:
        raise Failure("--shards and --jobs must be positive")
    only = str(Path(args.only).resolve()) if args.only else None
    ctx = prepare(args)
    out, total = ctx["out"], len(ctx["library"])
    # The frequencies of constants, which relevance weighs by, once per environment and one
    # environment at a time: counting walks every statement the environment imports.
    launch_all(1, [(ctx["project"], ctx["lib"], out, f"frequencies-e{e}", "DupSearch.Relevance",
                    "runFrequencies", env["imports"],
                    base_config(args, out / f"frequencies-e{e}.jsonl", env["assigned"]))
                   for e, env in enumerate(ctx["envs"])])
    tasks = []
    for e, env in enumerate(ctx["envs"]):
        # shards in proportion to the modules an environment handles
        shards = max(1, round(args.shards * len(env["assigned"]) / total))
        for k in range(shards):
            stem = f"search-e{e}-{k}"
            config = base_config(args, out / f"{stem}.jsonl", env["assigned"]) | {
                "heartbeats": args.heartbeats, "candidateHeartbeats": args.candidate_heartbeats,
                "star": args.star, "libraryStar": args.library_star,
                "relevantStar": args.relevant_star, "relevance": args.relevance,
                "gateTop": args.gate_top, "ownProof": args.own_proof,
                "definitionalHeartbeats": args.definitional_heartbeats, "relevantHeartbeats": args.relevant_heartbeats,
                "transparency": args.transparency, "depth": args.depth,
                "shard": k,
                "shards": shards, "only": only,
                "frequencies": str(out / f"frequencies-e{e}.jsonl")}
            tasks.append((ctx["project"], ctx["lib"], out, stem, "DupSearch.Search", "runSearch",
                          env["imports"], config))
    launch_all(args.jobs, tasks)
    summarize(out)


def cmd_index(args: argparse.Namespace) -> None:
    ctx = prepare(args)
    out = ctx["out"]
    tasks = [(ctx["project"], ctx["lib"], out, f"index-e{e}", "DupSearch.Normalize", "runIndex",
              env["imports"], base_config(args, out / f"index-e{e}.jsonl", env["assigned"]))
             for e, env in enumerate(ctx["envs"])]
    launch_all(1, tasks)
    summarize(out)


def origin(hit: dict, roots: list[str], exclude: list[str]) -> str:
    """Where the closing lemma comes from: `library` (a theorem of the scope), `excluded` (a
    theorem under a root but in an excluded module), `external` (a theorem of another package,
    as Mathlib), or `trivial` (not a theorem, or a fact of the language and its standard
    library)."""
    module = hit.get("lemma_module")
    if hit.get("lemma_kind") != "theorem" or module is None:
        return "trivial"
    under = lambda m, ps: any(m == p or m.startswith(p + ".") for p in ps)
    if under(module, roots):
        return "excluded" if under(module, exclude) else "library"
    return "trivial" if module.split(".")[0] in CORE_ROOTS else "external"


# How a hit reads, from the shape of its solution (`DupSearch/Shape.lean`), after the hand reading
# of the atoms run (README): the first reading whose test holds, in this order.
READINGS = {
    "unfolding": "true by unfolding: reflexivity closes it or one of the lemma's side goals, or "
                 "the lemma applies only up to a definition and is not relevant to it",
    "iff_direction": "one direction of an iff",
    "specialization": "the lemma at particular terms, or with side goals other lemmas prove: "
                      "an alias at the library's own notion or a special case worth keeping, "
                      "which the shape of the solution cannot tell apart",
    "unneeded_hypothesis": "a duplicate whose statement has a hypothesis it does not need",
    "duplicate": "a duplicate: the lemma at the theorem's own variables",
}


def reading(hit: dict, relevance: float) -> str | None:
    """The reading of a hit (`READINGS`); `None` for a record without a `shape`. `relevance` is
    the threshold of the run: a lemma that applies only beyond the search's transparency counts
    as a restatement up to a definition only when it is that relevant to the theorem, as the
    search's `relevant` phase decides."""
    shape = hit.get("shape")
    if shape is None:
        return None
    if shape["reflexive_lemma"] or shape["reflexive_side_goals"] or \
            (shape["unfolds"] and hit["relevance"] < relevance):
        return "unfolding"
    if hit["direction"] != "none":
        return "iff_direction"
    # Not `specific_levels`: a theorem about `Type u` that restates a lemma about `Sort u` is a
    # special case only in name.
    if not shape["head_is_lemma"] or shape["specific_args"] or shape["derived_side_goals"] \
            or shape["repeated_args"]:
        return "specialization"
    if shape["unused_hypotheses"]:
        return "unneeded_hypothesis"
    return "duplicate"


def environment_count(out: Path) -> int:
    path = out / "environments.json"
    if not path.is_file():
        raise Failure(f"{path} is missing")
    return len(json.loads(path.read_text()))


def summarize_scan(out: Path) -> dict | None:
    records = read_records(out / "scan.jsonl")
    if not records:
        return None
    pairs = defaultdict(list)
    for r in records:
        if r["record"] == "clash":
            pairs[tuple(dotted(tuple(m)) for m in r["modules"])].append(r["constant"])

    def declarations(constants: list[str]) -> list[str]:
        """The clashing declarations: the constants no other clashing constant of the pair is a
        prefix of, so that `X.casesOn`, `X.mk`, … count with `X`."""
        names = set(constants)
        return sorted(c for c in names
                      if not any(c.startswith(d + ".") for d in names if d != c))

    module_pairs = [{"first": a, "second": b, "declarations": declarations(cs),
                     "constants": sorted(cs)} for (a, b), cs in sorted(pairs.items())]
    return {
        "complete": records[-1]["record"] == "done",
        "modules_scanned": sum(r["record"] == "module" for r in records),
        "clashing_constants": sum(map(len, pairs.values())),
        "clashing_declarations": sum(len(p["declarations"]) for p in module_pairs),
        "clashing_module_pairs": module_pairs,
        "environments": environment_count(out),
    }


def summarize_search(out: Path) -> dict | None:
    files = sorted(out.glob("search-e*-*.jsonl"))
    if not files:
        return None
    starts, theorems, unfinished = [], [], []
    incomplete = []
    for e in range(environment_count(out)):
        env_files = sorted(out.glob(f"search-e{e}-*.jsonl"))
        env_starts, env_theorems = [], []
        for path in env_files:
            records = read_records(path)
            env_starts += [r for r in records if r["record"] == "start"]
            env_theorems += [r for r in records if r["record"] == "theorem"]
            if not records or records[-1]["record"] != "done":
                unfinished.append(path.name)
        if not env_starts or len(env_files) != env_starts[0]["config"]["shards"] \
                or len(env_theorems) != env_starts[0]["selected"]:
            incomplete.append(e)
        starts += env_starts
        theorems += env_theorems
    config = starts[0]["config"]
    roots, exclude = config["roots"], config["exclude"]
    outcomes = Counter(t["outcome"] for t in theorems)
    hits = [t | {"origin": origin(t, roots, exclude), "reading": reading(t, config["relevance"])}
            for t in theorems if t["outcome"] == "hit"]
    ms = sorted(t["ms"] for t in theorems)
    passes = [t for t in theorems if "normal_pass" in t]
    normal_hits = [t["normal_pass"] | {"name": t["name"], "module": t["module"], "sorry": t["sorry"],
                                       "origin": origin(t["normal_pass"], roots, exclude),
                                       "reading": reading(t["normal_pass"], config["relevance"])}
                   for t in passes if t["normal_pass"].get("outcome") == "hit"]
    return {
        "roots": roots, "exclude": exclude,
        "normal_pass_statuses": dict(Counter(t["normal_pass"]["status"] for t in passes)),
        "normal_hits_by_origin": dict(Counter(h["origin"] for h in normal_hits)),
        "normal_hits": sorted(normal_hits, key=lambda h: (h["origin"], h["module"], h["name"])),
        "simp_closed": sorted(({"name": t["name"], "used": t["normal_pass"]["used"]}
                               for t in passes if t["normal_pass"]["status"] == "closed"),
                              key=lambda c: c["name"]),
        "heartbeats": config["heartbeats"], "depth": config["depth"],
        "selected": sum(s["selected"] for s in starts if s["config"]["shard"] == 0),
        "searched": len(theorems),
        "complete": not unfinished and not incomplete,
        "unfinished_shards": unfinished,
        "incomplete_environments": incomplete,
        "outcomes": dict(outcomes),
        "sorried": sum(t["sorry"] for t in theorems),
        "hits_by_origin": dict(Counter(h["origin"] for h in hits)),
        "hits_by_phase": dict(Counter(h["phase"] for h in hits)),
        "hits_by_reading": dict(Counter(h["reading"] for h in hits if h["reading"])),
        "hits_one_way_iff": sum(h["direction"] != "none" for h in hits),
        "hits_derived_from_theorem": sum(h["uses"] for h in hits),
        "hits_on_sorried": sum(h["sorry"] for h in hits),
        "definitional": dict(Counter(t["definitional"] for t in theorems
                                     if t.get("definitional"))),
        "median_ms": ms[len(ms) // 2] if ms else None,
        "total_ms": sum(ms),
        "hits": sorted(hits, key=lambda h: (h["origin"], h["module"], h["name"])),
        "errors": [t for t in theorems if t["outcome"] == "error"],
    }


def summarize_index(out: Path) -> dict | None:
    files = sorted(out.glob("index-e*.jsonl"))
    if not files:
        return None
    theorems, complete = [], len(files) == environment_count(out)
    for path in files:
        records = read_records(path)
        theorems += [r for r in records if r["record"] == "theorem"]
        complete &= bool(records) and records[-1]["record"] == "done"
    groups = {}
    for key in ("exact", "insts"):
        by_hash = defaultdict(list)
        for t in theorems:
            by_hash[t[key]].append(t["name"])
        groups[key] = sorted(sorted(ns) for ns in by_hash.values() if len(ns) > 1)
    exact_sets = {frozenset(g) for g in groups["exact"]}
    exact_of = {t["name"]: t["exact"] for t in theorems}
    used_of = {t["name"]: t.get("normal_used", []) for t in theorems}
    # the confirmed classes of statements with one normal form, beyond what the exact hash
    # already groups (a class lives within one environment)
    classes = [c for path in files for r in read_records(path) if r["record"] == "normal_group"
               for c in r["classes"]]
    normal_only = sorted(sorted(c) for c in classes
                         if len(c) > 1 and len({exact_of[n] for n in c}) > 1)
    return {
        "complete": complete,
        "theorems": len(theorems),
        "normal_statuses": dict(Counter(t.get("normal_status", "off") for t in theorems)),
        "normal_only_groups": normal_only,
        "normal_used": {n: used_of[n] for g in normal_only for n in g},
        "simp_closed": sorted(({"name": t["name"], "used": t.get("normal_used", [])}
                               for t in theorems if t.get("normal_status") == "closed"),
                              key=lambda c: c["name"]),
        "exact_groups": groups["exact"],
        # groups that collide only once instance arguments are erased
        "insts_only_groups": [g for g in groups["insts"] if frozenset(g) not in exact_sets],
    }


def render(summary: dict) -> str:
    lines = ["# Duplicate search summary", ""]
    c, s, i = summary.get("scan"), summary.get("search"), summary.get("index")
    # The findings in the terms of clone detection (Roy and Cordy's types).
    lines += ["| Finding | Kind | Count |", "|---|---|---|"]
    if c:
        lines.append(f"| declarations two modules both make, incompatibly | name clash | "
                     f"{c['clashing_declarations']} in {len(c['clashing_module_pairs'])} module "
                     f"pairs |")
    if i:
        lines.append(f"| groups of theorems with the same statement up to renaming | Type 1–2 "
                     f"clone | {len(i['exact_groups'])} |")
        lines.append(f"| further groups equal only once instance arguments are erased (weak: "
                     f"erases typeclass hypotheses too) | Type 3, near miss | "
                     f"{len(i['insts_only_groups'])} |")
        lines.append(f"| further groups with the same normal form (simp, then canonical binder "
                     f"order) | Type 2, normalized | {len(i['normal_only_groups'])} |")
        lines.append(f"| statements simp proves outright | redundant unless simp API | "
                     f"{len(i['simp_closed'])} |")
    if s:
        for origin_, n in sorted(s["hits_by_origin"].items()):
            lines.append(f"| theorems an existing `{origin_}` lemma closes | Type 4, semantic "
                         f"| {n} |")
        own = s["hits_by_phase"].get("own_proof", 0)
        if own:
            lines.append(f"| of these, theorems whose own proof only applies the lemma | "
                         f"Type 4, by construction | {own} |")
        unfolding = s["hits_by_phase"].get("relevant", 0)
        if unfolding:
            lines.append(f"| of these, theorems closed only once definitions are unfolded, by a "
                         f"relevant lemma | Type 4, up to unfolding | {unfolding} |")
        for reading_, text in READINGS.items():
            n = s.get("hits_by_reading", {}).get(reading_, 0)
            if n:
                lines.append(f"| of these, read as {text} | Type 4, `{reading_}` | {n} |")
        for origin_, n in sorted(s["normal_hits_by_origin"].items()):
            lines.append(f"| further theorems an existing `{origin_}` lemma closes once "
                         f"normalized | Type 4, normalized | {n} |")
        for how, n in sorted(s.get("definitional", {}).items()):
            lines.append(f"| statements true by definition (`{how.replace('_', ', then ')}`) | "
                         f"definitional, not a duplicate | {n} |")
    lines.append("")
    if c:
        lines += [f"Scan: {c['modules_scanned']} modules read; {c['clashing_declarations']} "
                  f"declarations ({c['clashing_constants']} constants with their auxiliaries) "
                  f"are made incompatibly by two modules, so the library is split among "
                  f"{c['environments']} environment(s).", ""]
        for p in c["clashing_module_pairs"]:
            shown = ", ".join(f"`{n}`" for n in p["declarations"][:6])
            more = f" and {len(p['declarations']) - 6} more" if len(p["declarations"]) > 6 else ""
            lines.append(f"- {p['first']} vs {p['second']}: {shown}{more}")
        lines.append("")
    if s:
        lines += [
            f"Roots {', '.join(s['roots'])}" + (f", excluding {', '.join(s['exclude'])}"
                                                 if s["exclude"] else "")
            + f"; `maxHeartbeats` {s['heartbeats']} per theorem, `solve_by_elim` depth {s['depth']}.",
            "",
            f"- searched {s['searched']} of {s['selected']} theorems"
            + ("" if s["complete"] else " (**incomplete run**)"),
            f"- outcomes: " + ", ".join(f"{k} {v}" for k, v in sorted(s["outcomes"].items())),
            f"- hits by origin of the lemma: "
            + ", ".join(f"{k} {v}" for k, v in sorted(s["hits_by_origin"].items())),
            f"- hits by phase: "
            + ", ".join(f"{k} {v}" for k, v in sorted(s["hits_by_phase"].items()))
            + " (`relevant`: at default transparency)",
            f"- hits through one direction of an iff: {s['hits_one_way_iff']}; hits whose lemma "
            f"is proved from the theorem: {s['hits_derived_from_theorem']}; hits on sorried "
            f"theorems: {s['hits_on_sorried']}",
            f"- median {s['median_ms']} ms per theorem, {s['total_ms'] / 3.6e6:.2f} CPU-hours "
            f"in all",
            f"- hits by reading: "
            + ", ".join(f"{k} {v}" for k, v in sorted(s.get("hits_by_reading", {}).items())),
            "", "| origin | reading | theorem | lemma | dir | phase | relevance | uses | sorry "
            "| module |",
            "|---|---|---|---|---|---|---|---|---|---|",
        ]
        for h in s["hits"]:
            lines.append(f"| {h['origin']} | {h.get('reading') or ''} | `{h['name']}` | "
                         f"`{h['lemma']}` | {h['direction']} | "
                         f"{h['phase']} | {h['relevance']:.2f} | "
                         f"{'yes' if h['uses'] else ''} | {'yes' if h['sorry'] else ''} | "
                         f"{h['module']} |")
        if s["normal_hits"]:
            lines += ["", "Hits of the second pass, on the normal form (`used`: the simp lemmas "
                      "that reached it):", "", "| origin | theorem | lemma | dir | used | module |",
                      "|---|---|---|---|---|---|"]
            for h in s["normal_hits"]:
                lines.append(f"| {h['origin']} | `{h['name']}` | `{h['lemma']}` | {h['direction']} "
                             f"| {', '.join(h['used'])} | {h['module']} |")
        if s["errors"]:
            lines += ["", "Errors:", ""] + [f"- `{e['name']}`: {e['message'][:300]}"
                                            for e in s["errors"]]
        lines.append("")
    if i:
        lines += [f"Statement index: {i['theorems']} public theorems, "
                  f"{len(i['exact_groups'])} groups with the same statement, "
                  f"{len(i['insts_only_groups'])} more up to instance arguments"
                  + ("." if i["complete"] else " (**incomplete run**)."), ""]
        for title, key in (("Same statement", "exact_groups"),
                           ("Same statement up to instance arguments", "insts_only_groups")):
            if i[key]:
                lines += [f"{title}:", ""] + ["- " + ", ".join(f"`{n}`" for n in g)
                                              for g in i[key]] + [""]
        if i["normal_only_groups"]:
            lines += ["Same normal form (each with the simp lemmas that reached it):", ""]
            for g in i["normal_only_groups"]:
                lines.append("- " + ", ".join(
                    f"`{n}`" + (f" ({', '.join(i['normal_used'][n])})" if i["normal_used"][n] else "")
                    for n in g))
            lines.append("")
    return "\n".join(lines)


def summarize(out: Path) -> None:
    summary = {"scan": summarize_scan(out), "search": summarize_search(out),
               "index": summarize_index(out)}
    if not any(summary.values()):
        raise Failure(f"{out} holds no records")
    (out / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    (out / "summary.md").write_text(render(summary))
    print(f"wrote {out / 'summary.md'}", file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("search", "index"):
        p = sub.add_parser(name)
        p.add_argument("project")
        p.add_argument("--root", action="append", required=True,
                       help="a root module of the library; repeatable")
        p.add_argument("--exclude", action="append", default=[],
                       help="a module, with those under it, to leave out; repeatable")
        p.add_argument("--out", required=True)
        p.add_argument("--normalize-heartbeats", type=int, default=20000,
                       help="budget, in thousands, of simplifying a statement to its normal form "
                            "(simp, then canonical binder order); 0 turns normal forms off")
        if name == "search":
            p.add_argument("--only", help="file of theorem names to search, one per line")
            p.add_argument("--shards", type=int, default=3)
            p.add_argument("--jobs", type=int, default=3)
            p.add_argument("--heartbeats", type=int, default=200000,
                           help="per theorem, in thousands as maxHeartbeats counts them")
            p.add_argument("--candidate-heartbeats", type=int, default=5000,
                           help="per candidate lemma, in thousands; a candidate that exceeds it "
                                "is skipped")
            p.add_argument("--star", action="store_true",
                           help="fall back to the wildcard-indexed lemmas, as exact? does")
            p.add_argument("--no-library-star", dest="library_star", action="store_false",
                           help="do not try the library's own wildcard-indexed lemmas")
            p.add_argument("--no-relevant-star", dest="relevant_star", action="store_false",
                           help="do not try the other wildcard-indexed lemmas whose relevance to "
                                "the theorem reaches --relevance")
            p.add_argument("--relevance", type=float, default=RELEVANCE,
                           help="relevance to the theorem from which a candidate that did not "
                                "close it is tried again at default transparency, and from which "
                                "a wildcard-indexed lemma is tried; above 1, none is")
            p.add_argument("--relevant-heartbeats", type=int, default=RELEVANT_HEARTBEATS,
                           help="per candidate tried again for its relevance, in thousands")
            p.add_argument("--heuristic", action="store_true",
                           help=f"the cheap search: --gate-top {HEURISTIC['gate_top']} "
                                f"--own-proof --definitional-heartbeats "
                                f"{HEURISTIC['definitional_heartbeats']}, unless given otherwise")
            p.add_argument("--gate-top", type=int, default=None,
                           help="try only the candidates whose relevance (or relevance with the "
                                "library's definitions unfolded) reaches --relevance, or among "
                                "the K most relevant; 0 tries every candidate (the default)")
            p.add_argument("--own-proof", action="store_true", default=None,
                           help="report without searching a theorem whose proof only applies "
                                "another theorem to its variables and hypotheses")
            p.add_argument("--definitional-heartbeats", type=int, default=None,
                           help="budget, in thousands, of trying rfl and ext; rfl on each "
                                "statement, to label those true by definition; 0 does not try "
                                "(the default)")
            p.add_argument("--transparency", choices=["instances", "reducible", "default"],
                           default="instances",
                           help="for applying candidates and closing side goals; exact? uses "
                                "default")
            p.add_argument("--depth", type=int, default=6, help="solve_by_elim depth")
    p = sub.add_parser("summarize")
    p.add_argument("out")
    args = parser.parse_args()
    if args.command == "search":
        # Each setting the preset names takes the preset's value unless given.
        preset = HEURISTIC if args.heuristic else EXHAUSTIVE
        for key, value in preset.items():
            if getattr(args, key) is None:
                setattr(args, key, value)
    try:
        if args.command == "search":
            cmd_search(args)
        elif args.command == "index":
            cmd_index(args)
        else:
            summarize(Path(args.out).resolve())
    except Failure as e:
        sys.exit(f"dupsearch: {e}")


if __name__ == "__main__":
    main()

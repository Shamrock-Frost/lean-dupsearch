#!/usr/bin/env python3
"""Run both tools on the fixture project under each toolchain given (default: the oldest and
newest supported) and check every planted answer.

    test/test_fixture.py [TOOLCHAIN …]      e.g. leanprover/lean4:v4.27.0
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
FIXTURE = TOOL / "test" / "fixture"
DEFAULT = ["leanprover/lean4:v4.27.0", "leanprover/lean4:v4.33.0"]

# name -> expected fields of its search record; `lemma` may be a set of acceptable lemmas
SEARCH = {
    "Fixture.add_zero'": {"outcome": "hit", "origin": "trivial", "sorry": False},
    "Fixture.add_zero_sorry": {"outcome": "hit", "origin": "trivial", "sorry": True},
    "Fixture.double_ne_zero": {"outcome": "hit", "lemma": "Fixture.double_ne_zero'",
                               "origin": "library", "uses": True, "reading": "duplicate"},
    "Fixture.double_ne_zero'": {"outcome": "hit", "lemma": "Fixture.double_ne_zero",
                                "origin": "library", "uses": False, "reading": "duplicate"},
    "Fixture.double_ne_zero_private": {
        "outcome": "hit", "private": True, "origin": "library",
        "lemma": {"Fixture.double_ne_zero", "Fixture.double_ne_zero'"}},
    "Fixture.eq_zero_of_double_eq_zero": {"outcome": "hit", "lemma": "Fixture.double_eq_zero_iff",
                                          "direction": "mp", "origin": "library",
                                          "reading": "iff_direction"},
    "Fixture.double_add": {"outcome": "hit", "lemma": "Fixture.double_add_excluded",
                           "origin": "excluded", "uses": True},
    "Fixture.double_eq_zero_iff": {},
    "Fixture.Pt.ext": {"not_lemma": "Fixture.Pt.ext_iff"},
    # closed only by a star lemma of core (`Function.comp`), which the default search does not
    # try; `eq_of_rel` closes it at default transparency, but is not relevant to it
    "Fixture.refl_add": {"outcome": "miss"},
    "Fixture.refl_mul": {},
    "Fixture.odd_true": {"outcome": "hit", "origin": "trivial", "module": "Fixture.«Odd-Name»"},
    "Fixture.clashA_thm": {"outcome": "hit", "origin": "trivial", "module": "Fixture.ClashA"},
    "Fixture.clashB_thm": {"outcome": "hit", "origin": "trivial", "module": "Fixture.ClashB"},
    "Fixture.twin": {"module": {"Fixture.TwinA", "Fixture.TwinB"}},
    "Fixture.ord_a": {},
    "Fixture.ord_b": {},
    # `R (id n)` is `R n` only once `id` is unfolded: the relevant candidates, tried again at
    # default transparency, close it (without them, the normal form does: `check_relevance`)
    "Fixture.idA": {"outcome": "hit", "phase": "relevant",
                    "lemma": {"Fixture.idB", "Fixture.R_S"}, "reading": "duplicate"},
    "Fixture.idB": {},
    "Fixture.eq_of_rel": {"outcome": "hit", "lemma": "Fixture.eq_of_rel'",
                          "phase": "library_star", "uses": True},
    "Fixture.eq_of_rel'": {"outcome": "hit", "lemma": "Fixture.eq_of_rel",
                           "phase": "library_star", "uses": False},
    # a star lemma of core, tried for its relevance (without it, a miss: `check_relevant_star`)
    "Fixture.subsingleton_eq": {"outcome": "hit",
                                "lemma": {"Subsingleton.elim", "Subsingleton.allEq"},
                                "phase": "relevant_star", "origin": "trivial",
                                "reading": "duplicate"},
    # the readings of `Reading`; those of the own proofs are checked in `check_heuristic`
    "Fixture.double_succ_ne_zero": {"outcome": "hit", "lemma": "Fixture.double_ne_zero",
                                    "reading": "specialization"},
    "Fixture.add_zero_of_pos": {},
    "Fixture.tagged_add_zero": {},
    "Fixture.rel_iff_eq": {},
    "Fixture.Big.succ": {},
    "Fixture.Pt.swap_mk": {"outcome": "hit", "lemma": "Fixture.Pt.ext", "reading": "unfolding"},
}
# what the cheap search reads off the own proofs of `Reading` and `Basic`, all in phase `own_proof`
OWN_PROOF_READINGS = {
    "Fixture.double_ne_zero'": "duplicate",
    "Fixture.eq_zero_of_double_eq_zero": "iff_direction",
    "Fixture.add_zero_of_pos": "unneeded_hypothesis",
    # the hypothesis the solution does not mention is in the statement
    "Fixture.tagged_add_zero": "duplicate",
}
# own proofs that show only that the statement holds by unfolding: the cheap search searches
# these theorems instead, and names the lemma of the own proof
OWN_PROOF_REJECTED = {
    # reflexivity itself
    "Fixture.rel_iff_eq": "Iff.rfl",
    # closes it only once `Big` is unfolded, and is not relevant to it
    "Fixture.Big.succ": "Nat.lt_succ_of_lt",
}
# groups the normal form merges that the exact hash does not
NORMAL_GROUPS = [["Fixture.idA", "Fixture.idB"], ["Fixture.ord_a", "Fixture.ord_b"]]
# statements simp proves outright
SIMP_CLOSED = {"Fixture.add_zero'", "Fixture.add_zero_sorry"}
# the clashes the scan must find, as (constant, {module, module}): `twin` is a theorem in
# `TwinA` and `TwinB`, compatible copies, and a definition in `TwinDef`, which clashes with each
CLASHES = [("Fixture.clashing", {"Fixture.ClashA", "Fixture.ClashB"}),
           ("Fixture.twin", {"Fixture.TwinA", "Fixture.TwinDef"}),
           ("Fixture.twin", {"Fixture.TwinB", "Fixture.TwinDef"})]
ENVIRONMENTS = 2
INDEX_EXACT = [["Fixture.add_zero'", "Fixture.add_zero_sorry"],
               ["Fixture.double_ne_zero", "Fixture.double_ne_zero'"],
               ["Fixture.eq_of_rel", "Fixture.eq_of_rel'"]]
INDEX_INSTS_ONLY = [["Fixture.refl_add", "Fixture.refl_mul"]]


def check(toolchain: str, work: Path) -> list[str]:
    project = work / "fixture"
    shutil.copytree(FIXTURE, project, ignore=shutil.ignore_patterns(".lake"))
    (project / "lean-toolchain").write_text(toolchain + "\n")
    subprocess.run(["lake", "build"], cwd=project, check=True, capture_output=True)
    scope = ["--root", "Fixture", "--exclude", "Fixture.Excluded"]
    for cmd in (["search", *scope, "--shards", "2", "--jobs", "2"], ["index", *scope]):
        subprocess.run([sys.executable, str(TOOL / "dupsearch.py"), cmd[0], str(project),
                        *cmd[1:], "--out", str(work / cmd[0])], check=True)
    errors = []
    search = json.loads((work / "search" / "summary.json").read_text())["search"]
    if not search["complete"]:
        errors.append("search incomplete")
    records = {}
    for path in (work / "search").glob("search-*.jsonl"):
        for line in path.read_text().splitlines():
            r = json.loads(line)
            if r["record"] == "theorem":
                if r["name"] in records:
                    errors.append(f"{r['name']} searched twice")
                records[r["name"]] = r
    hits = {h["name"]: h for h in search["hits"]}
    if set(records) != set(SEARCH):
        errors.append(f"searched {sorted(records)}, expected {sorted(SEARCH)}")
    for name, want in SEARCH.items():
        got = hits.get(name, records.get(name))
        if got is None:
            continue
        for key, value in want.items():
            if key == "not_lemma":
                if got.get("lemma") == value:
                    errors.append(f"{name}: closed by {value}, which it generates")
            elif key in ("normal_status", "normal_outcome"):
                np = got.get("normal_pass") or {}
                have = np.get("status") if key == "normal_status" else np.get("outcome")
                if have != value:
                    errors.append(f"{name}: second pass {key} = {have!r}, expected {value!r}")
            elif isinstance(value, set):
                if got.get(key) not in value:
                    errors.append(f"{name}: {key} = {got.get(key)!r}, expected one of {value}")
            elif got.get(key) != value:
                errors.append(f"{name}: {key} = {got.get(key)!r}, expected {value!r}")
    for cmd in ("search", "index"):
        scan = json.loads((work / cmd / "summary.json").read_text())["scan"]
        found = [(c, {pair["first"], pair["second"]})
                 for pair in scan["clashing_module_pairs"] for c in pair["declarations"]]
        if found != CLASHES:
            errors.append(f"{cmd}: clashes {found}, expected {CLASHES}")
        if scan["environments"] != ENVIRONMENTS:
            errors.append(f"{cmd}: {scan['environments']} environments, expected {ENVIRONMENTS}")
    index = json.loads((work / "index" / "summary.json").read_text())["index"]
    if index["exact_groups"] != INDEX_EXACT:
        errors.append(f"index exact groups {index['exact_groups']}")
    if index["insts_only_groups"] != INDEX_INSTS_ONLY:
        errors.append(f"index groups up to instances {index['insts_only_groups']}")
    for g in NORMAL_GROUPS:
        if g not in index["normal_only_groups"]:
            errors.append(f"normal form does not group {g}: {index['normal_only_groups']}")
    closed = {c["name"] for c in index["simp_closed"]}
    if not SIMP_CLOSED <= closed:
        errors.append(f"simp-provable {sorted(closed)}, expected at least {sorted(SIMP_CLOSED)}")
    if index["theorems"] != len(SEARCH) - 1:  # the private theorem is not indexed
        errors.append(f"index has {index['theorems']} theorems")
    return errors


def check_star(work: Path) -> list[str]:
    """With `--star`, the wildcard-indexed lemmas are tried when no candidate applies, as
    `exact?` does: `Function.comp` then closes `refl_add`, in the star phase."""
    project = work / "fixture"
    out = work / "search-star"
    subprocess.run([sys.executable, str(TOOL / "dupsearch.py"), "search", str(project),
                    "--root", "Fixture", "--exclude", "Fixture.Excluded", "--only",
                    str(work / "only-star.txt"), "--star", "--out", str(out)], check=True)
    records = [json.loads(line) for path in out.glob("search-*.jsonl")
               for line in path.read_text().splitlines()]
    r = next((r for r in records if r.get("name") == "Fixture.refl_add"), None)
    if r is None or r["outcome"] != "hit" or r["stats"]["phase"] != "star":
        return [f"--star: refl_add gave {r and (r['outcome'], r['stats']['phase'])}"]
    return []


def check_relevance(work: Path) -> list[str]:
    """With no candidate relevant enough to try again (`--relevance 2`), the first pass misses
    `idA` and the pass on its normal form, where simp has rewritten `id n` to `n`, finds it."""
    project = work / "fixture"
    out = work / "search-norelevance"
    subprocess.run([sys.executable, str(TOOL / "dupsearch.py"), "search", str(project),
                    "--root", "Fixture", "--exclude", "Fixture.Excluded", "--only",
                    str(work / "only-relevance.txt"), "--relevance", "2", "--out", str(out)],
                   check=True)
    records = [json.loads(line) for path in out.glob("search-*.jsonl")
               for line in path.read_text().splitlines()]
    r = next((r for r in records if r.get("name") == "Fixture.idA"), None)
    np = (r or {}).get("normal_pass") or {}
    if r is None or r["outcome"] != "miss" or r["stats"]["relevant"] != 0 or \
            np.get("status") != "changed" or np.get("outcome") != "hit":
        return [f"--relevance 2: idA gave {r and (r['outcome'], np)}"]
    return []


def check_relevant_star(work: Path) -> list[str]:
    """Without the star lemmas tried for their relevance (`--no-relevant-star`), the search
    misses `subsingleton_eq`."""
    project = work / "fixture"
    out = work / "search-norelevantstar"
    subprocess.run([sys.executable, str(TOOL / "dupsearch.py"), "search", str(project),
                    "--root", "Fixture", "--exclude", "Fixture.Excluded", "--only",
                    str(work / "only-relevant-star.txt"), "--no-relevant-star", "--out", str(out)],
                   check=True)
    records = [json.loads(line) for path in out.glob("search-*.jsonl")
               for line in path.read_text().splitlines()]
    r = next((r for r in records if r.get("name") == "Fixture.subsingleton_eq"), None)
    if r is None or r["outcome"] != "miss" or r["stats"]["relevant_star"] != 0:
        return [f"--no-relevant-star: subsingleton_eq gave {r and r['outcome']}"]
    return []


def check_heuristic(work: Path) -> list[str]:
    """The cheap search (`--heuristic`) finds every theorem the exhaustive search finds; it reports
    a theorem whose proof only applies another (`eq_of_rel'`, `double_ne_zero'`) from that proof,
    with its direction and the reading of that proof (or searches it, when that proof shows only
    that it holds by unfolding), leaves candidates out by relevance, and labels the statements
    true by definition."""
    project = work / "fixture"
    out = work / "search-heuristic"
    subprocess.run([sys.executable, str(TOOL / "dupsearch.py"), "search", str(project),
                    "--root", "Fixture", "--exclude", "Fixture.Excluded", "--heuristic",
                    "--out", str(out)], check=True)
    def load(d: Path) -> dict:
        return {r["name"]: r for path in d.glob("search-*.jsonl")
                for line in path.read_text().splitlines()
                for r in [json.loads(line)] if r["record"] == "theorem"}
    exhaustive, heuristic = load(work / "search"), load(out)
    errors = [f"--heuristic: {n} is a {heuristic.get(n, {}).get('outcome')}"
              for n, r in exhaustive.items()
              if r["outcome"] == "hit" and heuristic.get(n, {}).get("outcome") != "hit"]
    for n, lemma in (("Fixture.eq_of_rel'", "Fixture.eq_of_rel"),
                     ("Fixture.double_ne_zero'", "Fixture.double_ne_zero")):
        r = heuristic.get(n, {})
        if (r.get("phase"), r.get("lemma")) != ("own_proof", lemma):
            errors.append(f"--heuristic: {n} gave {r.get('phase')} {r.get('lemma')}")
    readings = {h["name"]: h for h in
                json.loads((out / "summary.json").read_text())["search"]["hits"]}
    for n, want in OWN_PROOF_READINGS.items():
        h = readings.get(n, {})
        if (h.get("phase"), h.get("reading")) != ("own_proof", want):
            errors.append(f"--heuristic: {n} read {h.get('phase')} {h.get('reading')}, "
                          f"expected own_proof {want}")
    for n, lemma in OWN_PROOF_REJECTED.items():
        r = heuristic.get(n, {})
        if r.get("own_proof_rejected") != lemma or r.get("phase") == "own_proof":
            errors.append(f"--heuristic: {n} gave {r.get('phase')} {r.get('lemma')}, "
                          f"own_proof_rejected {r.get('own_proof_rejected')!r}")
    if heuristic.get("Fixture.eq_zero_of_double_eq_zero", {}).get("direction") != "mp":
        errors.append("--heuristic: the own proof of eq_zero_of_double_eq_zero is not read as mp")
    if not any(r["stats"]["gated"] for r in heuristic.values()):
        errors.append("--heuristic: the gate left no candidate out")
    for n, how in (("Fixture.refl_add", "rfl"), ("Fixture.Pt.ext", "ext_rfl"),
                   ("Fixture.double_ne_zero", None)):
        if heuristic.get(n, {}).get("definitional") != how:
            errors.append(f"--heuristic: {n} definitional "
                          f"{heuristic.get(n, {}).get('definitional')!r}, expected {how!r}")
    return errors


def check_lean_tests(toolchain: str, work: Path) -> list[str]:
    """Run `test/Memo.lean`, `test/Normal.lean` and `test/Relevance.lean` against the tool compiled with `toolchain`."""
    project = work / "fixture"
    lib = work / "search" / "lib"  # the tool as the driver compiled it for the fixture
    errors = []
    for test, ok in (("Memo.lean", "memo ok"), ("Normal.lean", "normal ok"),
                     ("Relevance.lean", "relevance ok")):
        proc = subprocess.run(["lake", "env", "lean", str(TOOL / "test" / test)], cwd=project,
                              env={**os.environ, "LEAN_PATH": str(lib)}, capture_output=True,
                              text=True, timeout=300)
        if proc.returncode != 0 or ok not in proc.stdout:
            errors.append(f"{test}: {proc.stdout}{proc.stderr}")
    return errors


def main() -> None:
    failed = False
    for toolchain in sys.argv[1:] or DEFAULT:
        with tempfile.TemporaryDirectory() as work:
            (Path(work) / "only-star.txt").write_text("Fixture.refl_add\n")
            (Path(work) / "only-relevance.txt").write_text("Fixture.idA\n")
            (Path(work) / "only-relevant-star.txt").write_text("Fixture.subsingleton_eq\n")
            errors = check(toolchain, Path(work)) + check_star(Path(work)) + \
                check_relevance(Path(work)) + check_relevant_star(Path(work)) + \
                check_heuristic(Path(work)) + \
                check_lean_tests(toolchain, Path(work))
        print(f"{toolchain}: " + ("ok" if not errors else "FAILED"))
        for e in errors:
            print("  " + e)
        failed |= bool(errors)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

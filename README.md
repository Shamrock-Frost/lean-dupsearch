# lean-dupsearch

Find theorems of a Lean library that restate an existing lemma, of the library itself or of its
dependencies (Mathlib), with three tools:

- **the module scan** reads the compiled library and finds the declarations that two of its
  modules both make, incompatibly. Such modules build on their own but cannot be imported
  together (a one-definition-rule violation, in C++ terms), so the scan also splits the library
  among as few environments as the clashes allow; the other two tools run in each.
- **the duplicate search** runs the library search behind `exact?` on the statement of every
  theorem, with the theorem itself excluded, and records which single lemma closes it. It finds
  restatements up to unfolding, symmetry, one direction of an iff, instance search and
  hypotheses the statement does not need. It is slow: about a second or more per theorem.
- **the statement index** hashes every public theorem's statement up to the names of bound
  variables and universe parameters, and again up to instance arguments; equal hashes are equal
  statements. It is cheap, and catches only literal restatements.

The index and the search complement each other. On the library they were written for, none of
the 352 search hits was a pair the index catches.

Both work on any Lake project whose toolchain is Lean 4.27.0 to 4.33.x, without changing it.

## Use

Build the project first (`lake build`), then:

```sh
./dupsearch.py search PATH/TO/PROJECT --root MyLib --exclude MyLib.Scratch \
    --shards 6 --jobs 3 --out out/search
./dupsearch.py index PATH/TO/PROJECT --root MyLib --exclude MyLib.Scratch \
    --out out/index
./dupsearch.py summarize out/search
```

- `--root M` (repeatable): the library is the modules equal to or under `M`: the sources
  `M.lean` and `M/**/*.lean`, which must all be built. Each process imports all of them, so the
  library needs no root file.
- `--exclude M` (repeatable): leave out the modules equal to or under `M`.
- `--only FILE`: search only the theorems named in `FILE`, one per line, for example those a
  branch added.
- `--shards N --jobs J`: deal the theorems to `N` processes in name order, `J` at a time (an
  environment that handles a fraction of the library gets that fraction of the shards). Each
  process loads the whole environment and builds its own discrimination tree, so memory, not
  cores, usually bounds `J`. On a shared machine, run the driver inside a resource-limited
  scope, e.g. `systemd-run --user --wait --pipe --same-dir -p MemoryMax=10G -p CPUQuota=800% …`.
- `--heartbeats K` (default 200000, as `maxHeartbeats` counts them): the budget of a theorem,
  spent on trying its candidate lemmas only (looking them up is not counted, see below).
- `--candidate-heartbeats K` (default 5000): the budget of one candidate; a candidate that
  exceeds it is skipped and recorded, and a miss with skipped candidates is incomplete.
- `--transparency instances|reducible|default` (default `instances`): at which candidates are
  applied and side goals closed. `exact?` uses `default`.
- `--star`: fall back to the lemmas indexed under a wildcard when no candidate applies, as
  `exact?` does.
- `--no-library-star`: do not try the library's own wildcard-indexed lemmas (tried by default,
  see below).
- `--no-relevant-star`: do not try the other wildcard-indexed lemmas whose relevance to the
  theorem is at least `--relevance` (tried by default unless `--star` is given, see below).
- `--relevance R` (default 0.3) and `--relevant-heartbeats K` (default 20000): a candidate that
  did not close the goal, and whose relevance to the theorem is at least `R`, is tried again at
  `default` transparency within `K`; a wildcard-indexed lemma is tried when its relevance is at
  least `R`. A relevance above 1 turns both off.
- `--depth D` (default 6): the depth of `solve_by_elim` on side goals, as `exact?` has it.

The tool's own Lean modules are compiled into the output directory with the project's toolchain
and found through `LEAN_PATH`. The project does not depend on this package.

## Output

The output directory holds:

- `scan.jsonl`, `search-eE-K.jsonl` and `index-eE.jsonl` (`E` the environment, `K` the shard):
  one JSON record per line, documented in `DupSearch/Modules.lean`, `DupSearch/Search.lean` and
  `DupSearch/Index.lean`;
- `frequencies-eE.jsonl`: how many theorems of environment `E` mention each constant, counted
  once before the search for its processes to weigh relevance by;
- `environments.json`: for each environment, the modules whose theorems it handles and the
  modules it imports;
- `run-search.json` and `run-index.json`: the project's commit and toolchain, and the command;
- `summary.json` and `summary.md`.

The summary opens with the findings in the terms of clone detection (Roy and Cordy's types):

| Finding | Kind |
|---|---|
| declarations two modules both make, incompatibly | name clash |
| theorems with the same statement up to renaming | Type 1–2 clone |
| theorems equal only once instance arguments are erased | Type 3, near miss: a weak signal, since erasing instance binders also erases typeclass hypotheses such as `[Module.Flat R M]` |
| theorems an existing lemma closes | Type 4, semantic |
| of these, theorems closed only at `default` transparency, by a relevant lemma | Type 4, up to unfolding |

It sorts each search hit by where the closing lemma comes from:

| origin | meaning |
|---|---|
| `library` | a theorem of the library: a duplicate inside it, or a corollary |
| `external` | a theorem of a dependency, as Mathlib: a restatement of upstream |
| `excluded` | a theorem under a root, in an excluded module |
| `trivial` | not a theorem (a constructor, a definition), or a lemma of `Init`, `Lean`, `Std` or `Batteries`: usually a statement true by unfolding |

A hit also records whether the lemma is used through one direction of an iff (`direction`),
whether the lemma's proof mentions the theorem (`uses`: a restatement derived from it), and
whether the theorem's own proof contains `sorry`.

A hit is a candidate, not a verdict. On the library the search was written for, a manual read
of its 352 hits found 46 duplicates, 46 corollaries (special cases, one-way forms of iffs) and
260 statements true by unfolding.

The summary therefore also reads each hit from the shape of its solution (`DupSearch/Shape.lean`;
`READINGS` in `dupsearch.py`), the first of these that applies:

| reading | the solution |
|---|---|
| `unfolding` | is reflexivity (`rfl`, `Iff.rfl`, a lemma concluding `r x x`), passes reflexivity to one of the lemma's side goals (`hom_ext (congrFun rfl)`, `_inj.mp rfl`), or applies the lemma only beyond the search's transparency when the lemma is not relevant to the theorem |
| `iff_direction` | uses one direction of an iff |
| `specialization` | applies the lemma at particular terms, or with side goals other lemmas prove: an alias at the library's own notion or a special case worth keeping, which the shape cannot tell apart |
| `unneeded_hypothesis` | applies the lemma at the theorem's own variables and leaves unused a hypothesis that the rest of the statement does not mention either |
| `duplicate` | applies the lemma at the theorem's own variables |

Checked against that manual read (atoms at `9d300b9`, the 352 theorems searched again with
`--heuristic`): the search hits 123 of them, 35 of which the manual read calls noise; the readings
keep 84 of the 92 duplicates and corollaries as anything but `unfolding` and read 3 of the 260
statements true by unfolding as real (precision 0.97, recall 0.91). The 8 lost are 4 misses and 4
special cases whose side goal is reflexivity (`of_eq h rfl`). `duplicate` and `specialization` do
not follow the manual read's line between duplicates and corollaries: 35 of its 46 duplicates
apply a lemma at the library's own notion (`mono_map_iff_mono (sliceForget X)`), which reads as a
`specialization`.

With `--heuristic`, a theorem whose own proof is reflexivity, or applies a lemma only beyond the
search's transparency that is not relevant to it, is searched rather than reported from its own
proof (`own_proof_rejected` names that lemma): such a proof shows only that the statement holds
by unfolding. On atoms it hid 6 of the hand-read corollaries behind `Iff.rfl`, `dif_pos` and the
like; searched, 4 of them are found with the hand-read lemma (3 read as real), and 18 theorems
the manual read calls noise stop being hits.

## How the search departs from `exact?`

- The theorem itself, and every constant generated beside it (equation lemmas, `@[reassoc]`
  forms, `ext_iff`, proof auxiliaries), are never candidates. A solution that mentions one is
  rejected, since instance search can find a theorem that is an instance.
- Deprecated lemmas are never candidates, on every toolchain. `exact?` skips them only from
  Lean 4.33 on, so runs on different toolchains would otherwise search different lemmas.
- The budget of a theorem is spent on trying candidates only. Looking candidates up expands the
  lazily built discrimination tree, whose cost depends on which theorems the process searched
  before; counting it made outcomes depend on the sharding (the first theorem of every process
  paid 22–24 s of tree building).
- Each candidate gets at most `--candidate-heartbeats`, and one that exceeds it is skipped
  rather than allowed to use up the theorem's budget.
- Candidates are applied at `instances` transparency, not `default`: deciding that a candidate
  does not apply then unfolds no definition, and most solutions that need one unfolded close
  the goal through definitional glue.
- A candidate that did not close the goal is tried again at `default` transparency, with a
  larger budget, when it is relevant to the theorem (below). This brings back the restatements
  that hold only up to a definition (`x ∈ separableClosure E K` is `IsSeparable E x`), and the
  candidates that needed more than `--candidate-heartbeats`, without bringing back the glue.
- The wildcard-indexed (`star`) lemmas are not all tried unless `--star` is given: those of the
  library itself are, being few, and the others are when they are relevant to the theorem.
  A restatement of a theorem that concludes `x = y` about a variable type is indexed only
  under the wildcard, and the 6000 star lemmas of Mathlib are otherwise glue (`Eq.to_iff`,
  `Function.comp`).
- A search that runs low on heartbeats is recorded as a timeout, not as a miss.

These choices were measured on a sample of 250 theorems of a second library, a large one built
on Mathlib that is not public (150 that had timed out under `exact?`'s settings, 50 hits, 50
misses):

| setting | hits | timeouts | CPU |
|---|---|---|---|
| `exact?`'s (`default` transparency, star lemmas, no candidate budget) | 50 | 150 | 2640 s |
| + candidate budget 20000, no star lemmas | 50 | 79 | 1731 s |
| + `instances` transparency | 28 | 37 | 1149 s |
| + candidate budget 5000 | 28 | 22 | 1035 s |

The 22 hits the transparency gives up are, read one by one, 20 statements true by unfolding
(closed through `rfl`, `congr_arg`, `Eq.to_iff` or an extensionality lemma) and 2 restatements
up to a definition (`id`, and a definition of the library). The star lemmas' only hits were
`Function.comp` closing statements true by `rfl`. No hit's winning candidate cost more than
1300 heartbeats (thousands). Lowering `--depth` to 2 removed 3 timeouts and lost 2 real
duplicates, so the depth stays at `exact?`'s 6. The timeouts left come from statements whose
shape (`_ ≠ 0`, `_ ≤ _` between ideals) matches hundreds of lemmas.

### Relevance

The relevance of a candidate to a theorem (`DupSearch/Relevance.lean`) uses the symbol-based
premise selection of automated theorem provers (MePo, SInE). It is the weighted Jaccard
similarity of the two statements' vocabularies. A vocabulary is the set of constants a
statement mentions outside instance arguments. Each constant is weighted by
`log((n + 1) / (k + 1))`, where `k` of the environment's `n` theorems mention it. A restatement is about
the same things as the theorem (`FiniteDimensional`, `CharP`, `separableClosure`). Glue is
about things every statement mentions (`SetLike`, `Eq`, `algebraMap`).

The threshold was calibrated on that second library, by scoring each hit of a search at
`exact?`'s settings against its theorem:

| hits of `exact?`'s settings | count | median relevance | ≥ 0.3 |
|---|---|---|---|
| kept at `instances` transparency, not through glue | 345 | 0.93 | 295 |
| lost at `instances` transparency, through glue (`rfl`, `congr_arg`, `ext`, …) | 279 | 0.05 | 10 |
| lost at `instances` transparency, otherwise | 64 | 0.14 | 19 |

Judged by the theorem and lemma (not by a reading of each proof), the 19 lost hits at 0.3 or
above are restatements, special cases and directions of iffs. Most of the 45 below are glue
that the term pattern does not catch (`Algebra.algebraMap_self_apply`, `AddMonCat.coe_of`,
`Quot.ind`). The exceptions are a few borderline cases between 0.19 and 0.3, such as
`AddCommGroup.DirectLimit.exists_of` from `Module.DirectLimit.exists_of`. The 10 glue hits at
0.3 or above are `ext` lemmas of the library's own structures closing its `mk_add`, `mk_smul`
and similar lemmas. A missed theorem has 2.6 candidates at 0.3 or
above on average (90th percentile 8).

On the full search of that library (4092 theorems), compared with the same search without the
relevance phase, the phase turned 26 misses into hits and 6 misses into timeouts, lost no hit,
and took 8% more CPU time. Of the 26, 13 are `ext` and `hom_ext` lemmas of the library's own
structures, the glue the threshold lets through; the other 13 are restatements and special
cases. Their last candidates took at most 2862 heartbeats (`last_heartbeats`, counted as
`maxHeartbeats` counts them) of the 20000 each may take. Each new timeout ran out of the
theorem's budget in this phase, after 9 to 15 seconds in the primary phase. Of the 6
restatements this phase was meant to recover, it recovered 5. The sixth restates
`eq_of_isNilpotent_sub_of_isIdempotentElem`,
a star lemma of Mathlib (its conclusion `e₁ = e₂` is indexed as `Eq * * *`), which that search
tried only with `--star`.

The star lemmas outside the library are therefore scored too, and tried when their relevance
reaches the threshold. On that library, of the 68 hits of `exact?`'s settings through such a
lemma, only that restatement scores 0.3 or above (relevance 1); the other 67 are `Eq.to_iff`,
`Function.comp`, `Quot.ind` and the like, at most 0.16. Of the 4051 theorems of the main
environment, 718 have a star lemma at 0.3 or above, 1596 in all (at most 25 for one theorem).
Scoring the 6121 star lemmas against each theorem goes through an index from each constant to
the lemmas that mention it; scoring them one by one took a quarter of a second per theorem. On
a sample of 401 theorems (the restatement, the 40 with the most relevant star lemmas, and 360
at random), the search with them found that restatement, changed no other outcome, and spent
2 seconds trying them and 5 more trying them again at `default` transparency, under 0.5% of
its CPU time.

## Limits

- The search sees only the lemmas of the environment: the library and what it imports. A
  restatement of a Mathlib lemma from a file the library never imports is missed.
- The library search finds a lemma that closes the statement in one step, with side goals
  closed by `solve_by_elim` from the hypotheses. A restatement that needs two lemmas, or
  rewriting, is missed.
- A hit is a candidate (see Output). Recall, the share of real duplicates found, is unknown.

## Tests

`test/test_fixture.py [TOOLCHAIN …]` builds `test/fixture`, a core-only project with planted
duplicates, a clash, a permitted repeated theorem and a module name that needs quoting, under
Lean 4.27.0 and 4.33.0 (or the toolchains given). It runs every tool and checks every planted
answer (including a restatement only the library's star lemmas reach, one only a relevant
star lemma of core reaches, one closed only at `default` transparency, and a glue solution the
relevance filter must keep out), then runs
the Lean tests. `test/Memo.lean` checks that the index's passes visit each distinct subterm
once: statements share subterms heavily, and a pass that walks them as trees takes exponential
time. `test/Normal.lean` checks the normal-form hash on universes, names and instance paths.
`test/Relevance.lean` checks that the frequency table reads back exactly, and that the index
that finds the relevant star lemmas finds what scoring every lemma finds.

## Origin

Ported from the duplicate search and statement index of the Atoms project, the library the
figures above were measured on. Its Lean sources are at
[Shamrock-Frost/atoms-formal](https://github.com/Shamrock-Frost/atoms-formal); its tooling and
the manual read of the hits are not public.

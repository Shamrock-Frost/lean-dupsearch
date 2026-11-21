import DupSearch.Relevance
import DupSearch.Shape

/-!
# The duplicate search

For every theorem of the library, run the library search behind `exact?` on its statement with
the theorem itself excluded, and record whether a single existing lemma closes it.

The search is `exact?`'s (`Lean.Meta.LibrarySearch.librarySearch`): introduce the statement's
binders, look up the candidate lemmas of the goal and of its symmetric form in the
discrimination tree of the environment, then apply each and close the side goals by
`solve_by_elim` from the hypotheses. It departs from `exact?` in these ways:

* the candidates omit the theorem itself and every constant generated beside it (`owner`), and
  a solution that mentions one of them is rejected, since instance search can find a theorem
  that is an instance;
* deprecated lemmas are never candidates, on every toolchain (`exact?` skips them from Lean
  4.33 on), so that runs on different toolchains search the same lemmas;
* the budget of a theorem (`Config.heartbeats`) is spent on trying candidates only: looking
  them up expands the lazily built discrimination tree, whose cost depends on which theorems
  the process searched before, and would make the outcome depend on the sharding;
* each candidate gets at most `Config.candidateHeartbeats`; a candidate that exceeds it is
  skipped and recorded, so that one runaway unification or instance search does not use up the
  theorem's budget;
* the lemmas indexed under a wildcard (`star` lemmas, whose conclusion is a bare variable or
  equation), which `exact?` falls back to when no candidate applies, are tried only with
  `Config.star`: they are thousands, they made a tenth of the timeouts of a measured run, and
  their only hits there were statements true by `rfl`. Without it, two kinds of star lemma are
  tried once the primary candidates miss, whether or not one of them applied, since the
  discrimination tree gives no other way to a restatement of a theorem whose conclusion is
  `x = y`: the star lemmas of the library itself, which are few (`Config.libraryStar`), and
  the others whose relevance to the theorem is at least `Config.relevance`
  (`Config.relevantStar`), most relevant first;
* candidates are applied, and side goals closed, at `Config.transparency`, by default
  `instances` (as `simp` and `rw` match) where `exact?` uses `default`: deciding that a
  candidate does not apply then unfolds no definition, which made the costliest failures of a
  measured run, and most solutions that need a definition unfolded close a goal by
  definitional glue (`SetLike.coe_eq_coe`, `Algebra.algebraMap_self_apply`);
* a candidate that did not close the goal is tried again at `default` transparency, with
  `Config.relevantHeartbeats`, when its relevance to the theorem (`DupSearch/Relevance.lean`)
  is at least `Config.relevance`, most relevant first: a lemma about the same things as the
  theorem may restate it up to a definition (`x ∈ separableClosure E K` and `IsSeparable E x`)
  or need more than `Config.candidateHeartbeats` to apply, while glue is about things every
  statement mentions;
* a search whose budget runs out is reported as a timeout rather than as a miss.

Three options make a cheaper search (`dupsearch.py search --heuristic`), which keeps the
duplicates the exhaustive one finds at a fraction of its cost:

* `Config.gateTop`: only the candidates relevant enough (`Scorer.gateRelevance` at least
  `Config.relevance`), or among the `gateTop` most relevant, are tried;
* `Config.ownProof`: a theorem whose own proof only applies another theorem (`restatedLemma`)
  is reported as restating it, in the phase `own_proof`, without a search, unless that theorem
  is reflexivity (`isReflexivityLemma`: `Iff.rfl`, `le_refl`, …) or closes the statement only
  beyond the search's transparency without being relevant to it (`acceptsAlone`): such a proof
  shows only that the statement holds by unfolding, which the search would not report, and
  hides a lemma the search may find (the theorem is then searched, and its record names the
  lemma in `own_proof_rejected`);
* `Config.definitionalHeartbeats`: each statement is labelled with how it holds by definition
  (`definitionalBy`), if it does; the label changes no outcome.

Each process writes one JSON object per line: a `start` record (with `warmup_ms`, the time the
discrimination tree took to build), one `theorem` record per theorem it was dealt, and a `done`
record. A `theorem` record has the fields

* `name`, `private`, `module`, `sorry` (whether the theorem's own proof contains `sorry`);
* `outcome`: `hit`, `miss`, `timeout` or `error`; a miss with skipped candidates is not a
  complete search;
* `ms` and `heartbeats` (in thousands) spent on the theorem;
* for a hit: `lemma`, `lemma_module` (`null` for a constant of no module), `lemma_kind`,
  `direction` (`none`, `mp` or `mpr`: the lemma is an iff used one way), `uses` (the lemma's
  proof mentions the theorem: a restatement derived from it), `term`, the solution, `phase`, the
  phase that found it (`own_proof`, `primary`, `library_star`, `relevant_star`, `star` or
  `relevant`, the last at `default` transparency), `relevance`, the lemma's relevance to the theorem,
  `proof_depth`, the depth of the solution (`proofDepth`), and `shape`, what the solution says
  about how the theorem follows from the lemma (`DupSearch/Shape.lean`), from which the driver
  reads the hit as a duplicate, a special case, and so on;
* for an error: `message`;
* with `Config.definitionalHeartbeats`: `definitional`, `rfl`, `ext_rfl` or `null`;
* with `Config.ownProof`, for a theorem searched although its own proof applies a lemma (see
  above): `own_proof_rejected`, that lemma;
* `stats`: where the search spent its effort (`DupSearch.Stats`);
* for a miss, when `Config.normalizeHeartbeats` is not `0`: `normal_pass`, the second pass on the
  statement's normal form (`normalPass`).
-/

open Lean Meta LibrarySearch

namespace DupSearch

/-- The outcome of one search. -/
inductive Outcome
  /-- A lemma closed the goal; the root metavariable is assigned. -/
  | hit (lem : Name) (mod : DeclMod)
  /-- No lemma closed the goal. -/
  | miss
  /-- The search stopped because the theorem's budget ran low. -/
  | timedOut

/-- Where one search spent its effort. It lives in a reference the caller holds, so that it
survives a search interrupted by an exception. -/
structure Stats where
  /-- The phase running: `lookup`, `primary` (the candidates the discrimination tree gives for
  the goal and its symmetric form), `library_star` (the library's lemmas indexed under a
  wildcard), `relevant_star` (the other lemmas indexed under a wildcard that are relevant to
  the theorem), `star` (all the other lemmas indexed under a wildcard) or `relevant` (the
  relevant candidates tried again). -/
  phase : String := "lookup"
  /-- The candidates of each phase, after the theorem's own constants and deprecated lemmas are
  left out. -/
  primary : Nat := 0
  /-- The candidates the gate (`Config.gateTop`) left out. -/
  gated : Nat := 0
  libraryStar : Nat := 0
  relevantStar : Nat := 0
  star : Nat := 0
  relevant : Nat := 0
  /-- The candidates tried, how many applied, and how many were skipped for exceeding their
  budget, with the first few skipped. -/
  tried : Nat := 0
  applied : Nat := 0
  skipped : Nat := 0
  skippedNames : Array Name := #[]
  /-- Milliseconds in each phase. -/
  lookupMs : Nat := 0
  /-- Milliseconds spent scoring the candidates' relevance for `costs`, before the budget. -/
  scoreMs : Nat := 0
  primaryMs : Nat := 0
  libraryStarMs : Nat := 0
  relevantStarMs : Nat := 0
  starMs : Nat := 0
  relevantMs : Nat := 0
  /-- Microseconds spent applying candidates (instantiating the lemma, unifying its conclusion
  with the goal, synthesizing its instances), and closing the side goals of those that applied
  (`solve_by_elim`), over all phases. -/
  applyUs : Nat := 0
  elimUs : Nat := 0
  /-- The candidates tried, the heartbeats (thousands) and the microseconds they took, by
  relevance band (`relevanceBands`) and by result (`resultKinds`): at index
  `(band * 4 + kind) * 3` the count, then the heartbeats, then the microseconds. -/
  costs : Array Nat := Array.replicate 36 0
  /-- The candidate being tried, and when it started (`IO.monoMsNow`). -/
  current : Name := .anonymous
  currentStart : Nat := 0
  /-- The heartbeats (thousands) of the last candidate tried: for a hit, the lemma that closed
  the goal. -/
  lastHeartbeats : Nat := 0
  /-- The slowest candidate tried, in milliseconds and heartbeats (thousands). -/
  slowest : Name := .anonymous
  slowestMs : Nat := 0
  slowestHeartbeats : Nat := 0

/-- The relevance bands of `Stats.costs`: below `0.1`, below `0.3`, and the rest. -/
def relevanceBands : Array String := #["<0.1", "0.1-0.3", ">=0.3"]

/-- The results of `Stats.costs`: the candidate did not apply, it applied but its side goals were
not closed, it ran out of its budget, or it closed the goal. -/
def resultKinds : Array String := #["no_apply", "side_goals_failed", "over_budget", "closed"]

/-- The band of a relevance in `relevanceBands`. -/
def relevanceBand (r : Float) : Nat := if r < 0.1 then 0 else if r < 0.3 then 1 else 2

/-- Count one candidate of `band` and `kind` that took `hb` heartbeats (thousands) and `us`
microseconds. -/
def addCost (costs : Array Nat) (band kind hb us : Nat) : Array Nat :=
  let i := (band * 4 + kind) * 3
  costs.modify i (· + 1) |>.modify (i + 1) (· + hb) |>.modify (i + 2) (· + us)

/-- `Stats.costs` as `{band: {kind: [count, heartbeats, microseconds]}}`. -/
def renderCosts (costs : Array Nat) : Json :=
  Json.mkObj <| (List.range 3).map fun b => (relevanceBands[b]!, Json.mkObj <|
    (List.range 4).map fun k =>
      let i := (b * 4 + k) * 3
      (resultKinds[k]!, toJson [costs[i]!, costs[i + 1]!, costs[i + 2]!]))

/-- A record's `stats` field; `now` closes the candidate in progress, if any. -/
def Stats.render (st : Stats) (now : Nat) : Json :=
  let name (n : Name) : Json := toJson (userName n).toString
  Json.mkObj [("phase", st.phase), ("primary", st.primary), ("gated", st.gated),
    ("library_star", st.libraryStar),
    ("relevant_star", st.relevantStar), ("star", st.star), ("relevant", st.relevant),
    ("tried", st.tried),
    ("applied", st.applied), ("skipped", st.skipped),
    ("skipped_names", toJson (st.skippedNames.map name)), ("lookup_ms", st.lookupMs),
    ("score_ms", st.scoreMs),
    ("primary_ms", st.primaryMs), ("library_star_ms", st.libraryStarMs),
    ("relevant_star_ms", st.relevantStarMs), ("star_ms", st.starMs),
    ("relevant_ms", st.relevantMs), ("apply_us", st.applyUs), ("elim_us", st.elimUs),
    ("costs", renderCosts st.costs),
    ("slowest", name st.slowest),
    ("slowest_ms", st.slowestMs), ("slowest_heartbeats", st.slowestHeartbeats),
    ("last_heartbeats", st.lastHeartbeats),
    ("interrupted_in", if st.current.isAnonymous then Json.null else name st.current),
    ("interrupted_after_ms", if st.current.isAnonymous then Json.null
      else toJson (now - st.currentStart))]

/-- A candidate as `skipped` records it: the goal it was tried on (the goal or its symmetric
form), the lemma, and the way an `iff` lemma was used. -/
abbrev CandidateKey := MVarId × Name × DeclMod

/-- Try the candidates in turn as `exact?` does, each within `candidateBudget` raw heartbeats
and all within the theorem's budget; `applied` records whether one applied, `skipped` the
candidates that exceeded their budget, and a solution counts only when `valid` accepts it. -/
def tryCandidates (cands : Array Candidate) (relevances : FloatArray)
    (depth candidateBudget : Nat) (shouldAbort valid : MetaM Bool) (applied : IO.Ref Bool)
    (skipped : IO.Ref (Std.HashSet CandidateKey)) (stats : IO.Ref Stats) : MetaM Outcome := do
  let cfg : ApplyConfig := { allowSynthFailures := true }
  let s ← saveState
  for h : i in [0:cands.size] do
    let ((goal, mctx), (name, mod)) := cands[i]
    let band := relevanceBand (relevances.get! i)
    if ← shouldAbort then
      s.restore
      return .timedOut
    let remaining ← getRemainingHeartbeats
    let budget := min candidateBudget remaining
    let t0 ← IO.monoMsNow
    let h0 ← IO.getNumHeartbeats
    let n0 ← IO.monoNanosNow
    -- When the candidate applied, if it did.
    let appliedAt ← IO.mkRef (none : Option Nat)
    stats.modify fun st => { st with current := name, currentStart := t0, tried := st.tried + 1 }
    let result ← withBudget budget do
      try
        setMCtx mctx
        let lem ← mkLibrarySearchLemma name mod
        let newGoals ← goal.apply lem cfg
        appliedAt.set (some (← IO.monoNanosNow))
        applied.set true
        stats.modify fun st => { st with applied := st.applied + 1 }
        let rest ← solveByElim [] (exfalso := false) newGoals (maxDepth := depth)
        if rest.isEmpty && (← valid) then pure (some (Outcome.hit name mod))
        else
          s.restore
          pure none
      catch _ =>
        s.restore
        pure none
    let t1 ← IO.monoMsNow
    let h1 ← IO.getNumHeartbeats
    let n1 ← IO.monoNanosNow
    let appliedNs ← appliedAt.get
    let n := appliedNs.getD n1
    stats.modify fun st => { st with applyUs := st.applyUs + (n - n0) / 1000 }
    stats.modify fun st => { st with elimUs := st.elimUs + (n1 - n) / 1000 }
    let kind := match result with
      | some (some _) => 3
      | none => 2
      | some none => if appliedNs.isSome then 1 else 0
    stats.modify fun st =>
      { st with costs := addCost st.costs band kind ((h1 - h0) / 1000) ((n1 - n0) / 1000) }
    stats.modify fun st =>
      let st := { st with current := .anonymous, lastHeartbeats := (h1 - h0) / 1000 }
      if t1 - t0 > st.slowestMs then
        { st with slowest := name, slowestMs := t1 - t0, slowestHeartbeats := (h1 - h0) / 1000 }
      else st
    match result with
    | some (some o) => return o
    | some none => pure ()
    | none =>
      s.restore
      -- The theorem's budget, not the candidate's, ran out.
      if budget < candidateBudget then return .timedOut
      skipped.modify (·.insert (goal, name, mod))
      stats.modify fun st =>
        let names := if st.skippedNames.size < 5 then st.skippedNames.push name
          else st.skippedNames
        { st with skipped := st.skipped + 1, skippedNames := names }
  return .miss

/-- How a theorem is searched (`Config`), with budgets in raw heartbeats. -/
structure Settings where
  depth : Nat
  budget : Nat
  candidateBudget : Nat
  star : Bool
  libraryStar : Bool
  relevantStar : Bool
  transparency : TransparencyMode
  relevance : Float
  relevantBudget : Nat
  gateTop : Nat

/-- The settings a configuration names. -/
def Config.settings (c : Config) : Settings :=
  { depth := c.depth, budget := c.heartbeats * 1000,
    candidateBudget := c.candidateHeartbeats * 1000, star := c.star,
    libraryStar := c.libraryStar, relevantStar := c.relevantStar,
    transparency := c.transparencyMode,
    relevance := c.relevance, relevantBudget := c.relevantHeartbeats * 1000,
    gateTop := c.gateTop }

/-- What the searches of one process share. -/
structure Searcher where
  settings : Settings
  scorer : Scorer
  /-- Whether a constant was declared in a module of the library. -/
  ofLibrary : Name → Bool
  /-- The library's star lemmas that are not deprecated, in the order `getStarLemmas` gives
  them; collected once, since sifting every star lemma of the environment costs seconds. -/
  libraryStars : Array (Name × DeclMod)
  /-- The other star lemmas that are not deprecated, to be scored by relevance; empty unless
  `Settings.relevantStar` holds and `Settings.star` does not. -/
  otherStars : Pool (Name × DeclMod)

/-- The searcher of a configuration, once the discrimination tree is built. -/
def Searcher.new (config : Config) (scorer : Scorer) : MetaM Searcher := do
  let env ← getEnv
  let settings := config.settings
  let ofLibrary (n : Name) := (moduleOf env n).any config.scope.inLibrary
  let stars := (← getStarLemmas).filter (!Linter.isDeprecated env ·.1)
  let libraryStars := stars.filter (ofLibrary ·.1)
  let others := if settings.relevantStar && !settings.star then stars.filter (!ofLibrary ·.1)
    else #[]
  let otherStars := Pool.new scorer.frequencies
    (← others.mapM fun (n, m) => return ((n, m), ← scorer.vocabularyOf n))
  return { settings, scorer, ofLibrary, libraryStars, otherStars }

/-- `exact?`'s library search on `goal`, never trying a constant that `exclude` rejects or that
is deprecated, and never accepting a solution of `root` that mentions a constant `exclude`
rejects. The candidates are looked up without a budget; trying them, in the phases of the
module docs, gets `sr.settings.budget` raw heartbeats in all. The relevance of a candidate is
to a statement of vocabulary `statement`. -/
def search (root : Expr) (goal : MVarId) (sr : Searcher) (statement : NameSet)
    (exclude : Name → Bool) (stats : IO.Ref Stats) : MetaM Outcome := do
  let env ← getEnv
  let s := sr.settings
  let candidate (n : Name) := !exclude n && !Linter.isDeprecated env n
  let applied ← IO.mkRef false
  let skipped ← IO.mkRef ({} : Std.HashSet CandidateKey)
  let valid := return !(← instantiateMVars root).getUsedConstants.any exclude
  let t0 ← IO.monoMsNow
  let cands := (← librarySearchSymm libSearchFindDecls goal).filter (candidate ·.2.1)
  let mctx ← getMCtx
  -- The gate: the candidates relevant enough, or among the most relevant, in their order.
  let all := cands.size
  let cands ← if s.gateTop == 0 then pure cands else do
    let unfolded ← sr.scorer.unfold statement
    let mut score : Std.HashMap Name Float := {}
    for (_, (n, _)) in cands do
      unless score.contains n do
        score := score.insert n (← sr.scorer.gateRelevance statement unfolded n)
    let ranked := score.toArray.qsort fun (n₁, r₁) (n₂, r₂) =>
      r₁ > r₂ || (r₁ == r₂ && n₁.quickLt n₂)
    let top := (ranked.extract 0 s.gateTop).foldl (fun t (n, _) => t.insert n) ({} : NameSet)
    pure <| cands.filter fun (_, (n, _)) => score.getD n 0 ≥ s.relevance || top.contains n
  stats.modify ({ · with gated := all - cands.size })
  let libraryStars := if !s.libraryStar then #[] else
    sr.libraryStars.filter (!exclude ·.1) |>.map ((goal, mctx), ·)
  let relevantStars := sr.otherStars.relevant sr.scorer.frequencies statement s.relevance
    |>.filter (candidate ·.2.1)
  let relevantStarsRel := relevantStars.foldl (fun a (r, _) => a.push r) FloatArray.empty
  let relevantStars := relevantStars.map ((goal, mctx), ·.2)
  let t1 ← IO.monoMsNow
  stats.modify fun st =>
    { st with primary := cands.size, libraryStar := libraryStars.size, lookupMs := t1 - t0 }
  stats.modify ({ · with relevantStar := relevantStars.size })
  -- The relevance of each candidate, for `Stats.costs`, scored before the budget starts.
  let relevancesOf (cs : Array Candidate) : MetaM FloatArray :=
    cs.foldlM (init := FloatArray.empty) fun a (_, (n, _)) =>
      return a.push (← sr.scorer.relevance statement n)
  let candsRel ← relevancesOf cands
  let libraryStarsRel ← relevancesOf libraryStars
  let t2 ← IO.monoMsNow
  stats.modify ({ · with scoreMs := t2 - t1 })
  let outcome ← withBudget s.budget do
    let shouldAbort ← mkHeartbeatCheck 10
    -- Try `cs` at `t`, each within `budget`, as `phase`; `record` stores the time taken.
    let run (phase : String) (t : TransparencyMode) (cs : Array Candidate) (rels : FloatArray)
        (budget : Nat) (record : Stats → Nat → Stats) : MetaM Outcome := do
      stats.modify ({ · with phase := phase })
      let t0 ← IO.monoMsNow
      let o ← withTransparency t <|
        tryCandidates cs rels s.depth budget shouldAbort valid applied skipped stats
      let t1 ← IO.monoMsNow
      stats.modify (record · (t1 - t0))
      return o
    let o ← run "primary" s.transparency cands candsRel s.candidateBudget
      ({ · with primaryMs := · })
    unless o matches .miss do return o
    -- `exact?` falls back to the star lemmas when no primary candidate applied.
    let primaryApplied ← applied.get
    let o ← run "library_star" s.transparency libraryStars libraryStarsRel s.candidateBudget
      ({ · with libraryStarMs := · })
    unless o matches .miss do return o
    let o ← run "relevant_star" s.transparency relevantStars relevantStarsRel
      s.candidateBudget ({ · with relevantStarMs := · })
    unless o matches .miss do return o
    let mut tried := cands ++ libraryStars ++ relevantStars
    if s.star && !primaryApplied then
      let others := (← getStarLemmas).filter (fun (n, _) =>
        candidate n && !(s.libraryStar && sr.ofLibrary n)) |>.map ((goal, mctx), ·)
      stats.modify ({ · with star := others.size })
      let o ← run "star" s.transparency others (← relevancesOf others) s.candidateBudget
        ({ · with starMs := · })
      unless o matches .miss do return o
      tried := tried ++ others
    -- The relevant candidates, most relevant first, ties in the order they were tried. At
    -- `default` transparency already, only the candidates that ran out of budget are new.
    let skippedNow ← skipped.get
    let mut scored : Array (Float × Nat) := #[]
    for h : i in [0:tried.size] do
      let ((g, _), (n, m)) := tried[i]
      if s.transparency == .default && !skippedNow.contains (g, n, m) then continue
      let r ← sr.scorer.relevance statement n
      if r ≥ s.relevance then scored := scored.push (r, i)
    let order := scored.qsort fun (r₁, i₁) (r₂, i₂) => r₁ > r₂ || (r₁ == r₂ && i₁ < i₂)
    let again := order.map fun (_, i) => tried[i]!
    let againRel := order.foldl (fun a (r, _) => a.push r) FloatArray.empty
    stats.modify ({ · with relevant := again.size })
    run "relevant" .default again againRel s.relevantBudget ({ · with relevantMs := · })
  return outcome.getD .timedOut

/-- A one-line rendering of an expression, cut at 400 characters. -/
def oneLine (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  let s := " ".intercalate (s.splitOn "\n" |>.map String.trimAscii |>.map toString)
  return if s.length > 400 then (s.take 400).toString ++ " …" else s

/-- The direction of a lemma used through `Iff`. -/
def directionString : DeclMod → String
  | .none => "none" | .mp => "mp" | .mpr => "mpr"

/-- The depth of a proof: `0` for a hypothesis or a constant, else one more than the deepest of
the proofs it applies its head to, under binders, leaving out instance arguments (instance search
finds them, not `solve_by_elim`, and a class can be a proposition). A solution `lem h₁ h₂` from
hypotheses has depth `1`; each side goal `solve_by_elim` closed with a lemma adds a level, and
so do the `Eq.symm` or `Iff.mp` that the symmetric goal or an `iff` lemma wrap a solution in. -/
partial def proofDepth (e : Expr) : MetaM Nat := do
  match e with
  | .mdata _ b => proofDepth b
  | .lam .. => lambdaTelescope e fun _ b => proofDepth b
  | .letE _ _ v b _ => proofDepth (b.instantiate1 v)
  | _ =>
    let args := e.getAppArgs
    if args.isEmpty then return 0
    let info ← getFunInfoNArgs e.getAppFn args.size
    let mut d := 0
    for h : i in [0:args.size] do
      if info.paramInfo[i]?.any (·.binderInfo.isInstImplicit) then continue
      if ← isProof args[i] then d := max d (← proofDepth args[i])
    return d + 1

/-- The fields of a hit's record that describe its lemma `lem`, used as `mod` says, for the
theorem `thm`. -/
def lemmaFields (env : Environment) (thm lem : Name) (mod : DeclMod) : List (String × Json) :=
  let info? := env.find? lem
  let uses := match info? >>= (·.value? (allowOpaque := true)) with
    | some v => v.getUsedConstants.contains thm
    | none => false
  [("lemma", toJson (userName lem).toString),
    ("lemma_module", toJson ((moduleOf env lem).map toString)),
    ("lemma_kind", toJson ((info?.map kindOf).getD "unknown")),
    ("direction", toJson (directionString mod)), ("uses", toJson uses)]

/-- The theorem a proof merely applies, if it does, and the direction it uses it in: under its
binders, and past the `Eq.symm`, `Iff.symm`, `Iff.mp` and `Iff.mpr` that turn a lemma around,
the proof is a theorem applied to bound variables in its explicit arguments (its implicit and
instance arguments may be anything: unification and instance search determine them). A theorem
with such a proof restates the theorem it applies, by construction. An `Iff.symm` under an
`Iff.mp` turns it into an `Iff.mpr`, and back. -/
partial def restatedLemma (env : Environment) (proof : Expr) (mod : DeclMod := .none) :
    Option (Name × DeclMod) :=
  match proof with
  | .lam _ _ b _ | .mdata _ b => restatedLemma env b mod
  | e =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const c _ =>
      if c == ``Eq.symm && args.size == 4 then restatedLemma env args[3]! mod
      else if c == ``Iff.symm && args.size == 3 then
        restatedLemma env args[2]! (match mod with | .mp => .mpr | .mpr => .mp | .none => .none)
      else if (c == ``Iff.mp || c == ``Iff.mpr) && args.size ≥ 3 && mod matches .none then
        if (args.extract 3 args.size).all (·.isBVar) then
          restatedLemma env args[2]! (if c == ``Iff.mp then .mp else .mpr)
        else none
      else
        let infos := paramInfos env c
        let applied := (List.range args.size).all fun i =>
          args[i]!.isBVar || infos[i]?.any (!·.isExplicit)
        if (env.find? c matches some (.thmInfo _)) && applied then some (c, mod) else none
    | _ => none

/-- Whether the search, given only the lemma `lem` used as `mod` says, closes `type` (a
theorem's statement) at the settings' transparency within one candidate's budget: whether a
restatement the theorem's own proof shows (`restatedLemma`) is one the search would accept, or
holds only up to an unfolding the search does not make. -/
def acceptsAlone (type : Expr) (lem : Name) (mod : DeclMod) (s : Settings)
    (exclude : Name → Bool) : MetaM Bool := do
  let root ← mkFreshExprMVar type
  let (_, goal) ← root.mvarId!.intros
  goal.withContext do
    let cands ← librarySearchSymm (fun _ => pure #[(lem, mod)]) goal
    let applied ← IO.mkRef false
    let skipped ← IO.mkRef ({} : Std.HashSet CandidateKey)
    let stats ← IO.mkRef ({} : Stats)
    let valid := return !(← instantiateMVars root).getUsedConstants.any exclude
    let o ← withBudget s.budget do
      let shouldAbort ← mkHeartbeatCheck 10
      withTransparency s.transparency <| tryCandidates cands
        (cands.foldl (fun a _ => a.push 0) FloatArray.empty) s.depth s.candidateBudget
        shouldAbort valid applied skipped stats
    return o matches some (.hit ..)

/-- How a statement holds by definition, if it does within `budget` raw heartbeats for each
attempt: by `rfl`, or by `ext` followed by `rfl` on every goal it leaves. -/
def definitionalBy (type : Expr) (budget : Nat) : MetaM (Option String) := do
  let root ← mkFreshExprMVar type
  let (_, goal) ← root.mvarId!.intros
  let attempts : List (String × Syntax) := [("rfl", ← `(tactic| rfl)),
    ("ext_rfl", ← `(tactic| (ext <;> rfl)))]
  for (label, tac) in attempts do
    let s ← saveState
    let closed ← withBudget budget <| tryCatchRuntimeEx
      (do
        let rest ← Elab.Term.TermElabM.run' <| Elab.Tactic.run goal (Elab.Tactic.evalTactic tac)
        return rest.isEmpty)
      fun e => if e.isMaxHeartbeat then throw e else pure false
    s.restore
    if closed == some true then return some label
  return none

/-- Search for the statement of one theorem; return the outcome's fields of its record. -/
def searchTheorem (thm : Name) (type : Expr) (sr : Searcher) (stats : IO.Ref Stats) :
    MetaM (List (String × Json)) := do
  let env ← getEnv
  let root ← mkFreshExprMVar type
  let (_, goal) ← root.mvarId!.intros
  let statement := vocabulary env type
  let outcome ← goal.withContext <|
    search root goal sr statement (fun c => owner env c == owner env thm) stats
  match outcome with
  | .miss => return [("outcome", "miss")]
  | .timedOut => return [("outcome", "timeout")]
  | .hit lem mod =>
    let solution := (← instantiateMVars root).headBeta
    let phase := (← stats.get).phase
    -- Beyond the search's transparency only in the `relevant` phase, which retries at `default`.
    let unfolds := phase == "relevant" && sr.settings.transparency != .default
    return [("outcome", toJson "hit")] ++ lemmaFields env thm lem mod ++
      [("term", toJson (← oneLine solution)), ("phase", toJson phase),
        ("relevance", toJson (← sr.scorer.relevance statement lem)),
        ("proof_depth", toJson (← proofDepth solution)),
        ("shape", (← shapeOf type solution lem mod).render unfolds)]

/-- The second pass of a theorem the first missed: simplify its statement to the normal form of
`DupSearch/Normalize.lean` and, when that changed it, search the normal form. The record says
whether simp proved the statement outright (`closed`), changed it, left it the same or ran out
of budget, with the simp lemmas used (and among them, `used_unfolds`, the unfoldings of the
library's definitions), the milliseconds simp took (`normalize_ms`) and the outcome of the
second search. -/
def normalPass (thm : Name) (type : Expr) (config : Config) (sr : Searcher) : MetaM Json := do
  let t0 ← IO.monoMsNow
  let normal ← simpNormal thm type config.scope.inLibrary (config.normalizeHeartbeats * 1000)
  let t1 ← IO.monoMsNow
  let ms : String × Json := ("normalize_ms", toJson (t1 - t0))
  -- The simp lemmas used that are unfoldings of the library's definitions.
  let env ← getEnv
  let unfolds (used : Array Name) : String × Json := ("used_unfolds", namesJson <| used.filter
    fun n => (moduleOf env n).any config.scope.inLibrary && (env.find? n matches some (.defnInfo _)))
  match normal with
  | .closed used =>
    return Json.mkObj [("status", "closed"), ("used", namesJson used), unfolds used, ms]
  | .failed _ => return Json.mkObj [("status", "failed"), ms]
  | .normal t used changed =>
    if !changed then
      return Json.mkObj [("status", "same"), ("used", namesJson used), unfolds used, ms]
    let stats ← IO.mkRef ({} : Stats)
    let fields ← searchTheorem thm t sr stats
    let head : List (String × Json) :=
      [("status", "changed"), ("used", namesJson used), unfolds used, ms]
    return Json.mkObj <| head ++ fields ++ [("stats", (← stats.get).render (← IO.monoMsNow))]

/-- Run the search a configuration file describes. -/
def runSearch (configPath : String) : CoreM Unit := withoutOptions do
  let config ← Config.load configPath
  let env ← getEnv
  let emit ← openOutput config.output
  let only : Option (Std.HashSet String) ← match config.only with
    | none => pure none
    | some path => do
      let lines := (← IO.FS.readFile path).splitOn "\n" |>.map (·.trimAscii.toString)
      pure (some (Std.HashSet.ofList (lines.filter (!·.isEmpty))))
  let selected := (libraryTheorems env config.scope (privates := true)).filter fun (n, _, _) =>
    only.all (·.contains (userName n).toString)
  let mine := (Array.range selected.size).filter (· % config.shards == config.shard)
  -- Build the discrimination tree once, before the first theorem.
  let w0 ← IO.monoMsNow
  unlimited (discard (libSearchFindDecls (mkConst ``True)).run')
  let w1 ← IO.monoMsNow
  let scorer ← Scorer.new config.scope.inLibrary config.frequencies
  let sr ← unlimited (Searcher.new config scorer).run'
  emit <| Json.mkObj [("record", "start"), ("config", toJson config),
    ("selected", selected.size), ("dealt", mine.size), ("warmup_ms", w1 - w0)]
  let mut counts : Std.HashMap String Nat := {}
  for i in mine do
    let (n, m, val) := selected[i]!
    let base : List (String × Json) := [("record", "theorem"),
      ("name", toJson (userName n).toString), ("private", isPrivateName n),
      ("module", toJson m.toString), ("sorry", val.value.hasSorry)]
    let t0 ← IO.monoMsNow
    let h0 ← IO.getNumHeartbeats
    let stats ← IO.mkRef ({} : Stats)
    let restated := if !config.ownProof then none else
      (restatedLemma env val.value).filter (owner env ·.1 != owner env n)
    let fields ← withoutModifyingEnv <| unlimited <| tryCatchRuntimeEx
      (match restated with
        | some (lem, mod) => (do
            stats.modify ({ · with phase := "own_proof" })
            let accepted ← acceptsAlone val.type lem mod sr.settings
              (fun c => owner env c == owner env n)
            let relevance ← sr.scorer.relevance (vocabulary env val.type) lem
            if (← isReflexivityLemma lem) || (!accepted && relevance < sr.settings.relevance)
            then
              stats.set {}
              let fields ← searchTheorem n val.type sr stats
              return fields ++ [("own_proof_rejected", toJson (userName lem).toString)]
            return [("outcome", toJson "hit")] ++ lemmaFields env n lem mod ++
              [("term", toJson (← oneLine val.value)), ("phase", toJson "own_proof"),
                ("relevance", toJson relevance),
                ("proof_depth", toJson (← proofDepth val.value)),
                ("shape", (← shapeOf val.type val.value lem mod).render !accepted)]).run'
        | none => (searchTheorem n val.type sr stats).run')
      fun e => do
        let msg := (← e.toMessageData.toString).replace "\n" " "
        return ([("outcome", "error"), ("message", toJson msg)] : List (String × Json))
    let definitional ← if config.definitionalHeartbeats == 0 then pure [] else do
      let how ← withoutModifyingEnv <| unlimited <| tryCatchRuntimeEx
        ((definitionalBy val.type (config.definitionalHeartbeats * 1000)).run')
        fun _ => pure none
      pure [("definitional", toJson how)]
    let outcome := match (fields.lookup "outcome" : Option Json) with
      | some (.str s) => s
      | _ => "error"
    counts := counts.insert outcome (counts.getD outcome 0 + 1)
    let normal ← if outcome != "miss" || config.normalizeHeartbeats == 0 then pure [] else do
      let j ← withoutModifyingEnv <| unlimited <|
        tryCatchRuntimeEx ((normalPass n val.type config sr).run') fun e => do
          let msg := (← e.toMessageData.toString).replace "\n" " "
          return Json.mkObj [("status", "error"), ("message", toJson msg)]
      pure [("normal_pass", j)]
    let t1 ← IO.monoMsNow
    let h1 ← IO.getNumHeartbeats
    emit <| Json.mkObj <| base ++ fields ++ definitional ++ normal ++
      [("ms", toJson (t1 - t0)), ("heartbeats", toJson ((h1 - h0) / 1000)),
        ("stats", (← stats.get).render t1)]
  emit <| Json.mkObj [("record", "done"),
    ("counts", Json.mkObj (counts.toList.map fun (k, v) => (k, toJson v)))]

end DupSearch

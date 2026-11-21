import DupSearch.Basic

/-!
# The shape of a solution

What a search hit's solution says about how the theorem follows from the lemma. The driver reads
a hit from these facts (`dupsearch.py`, `reading`) after the hand reading of the 352 hits of the
atoms run: as a duplicate, a duplicate with a hypothesis it does not need, the lemma at
particular terms (a specialization), one direction of an iff, or a statement true by unfolding
that the lemma only seems to restate.

A solution is `fun xs => w (lem as)`, where `xs` are the theorem's binders, `lem` the lemma, `as`
its arguments, and `w` the wrappers that turn a lemma around: `Eq.symm`, `Iff.symm` (the search
tries the symmetric goal) and `Iff.mp` or `Iff.mpr` (an iff used one way), with the hypotheses
the one-way form takes. The facts are

* `wrappers`: the wrappers, outermost first (`symm`, `mp`, `mpr`);
* `head_is_lemma`: whether, past the wrappers, the solution is `lem` applied;
* `reflexive_lemma`: whether `lem` is reflexivity itself (`isReflexivityLemma`: `rfl`, `Iff.rfl`,
  `id`, `trivial`, or a lemma concluding `r x x`);
* `reflexive_side_goals`: how many of the proofs passed to `lem` (or to its one-way form) are
  reflexivity (`isReflexive`): side goals that hold by unfolding, as in `hom_ext (congrFun rfl)`;
* `derived_side_goals`: how many of those proofs are neither a hypothesis of the theorem nor
  reflexivity: `solve_by_elim` proved them with further lemmas;
* `schematic_lemma`: whether `lem`'s conclusion, in the direction used, says nothing about any
  particular term (`schematic`): a bare variable applied (`Classical.choose_spec`,
  `of_decide_eq_true`), or an equation, `HEq` or iff between two variables (an extensionality,
  injectivity or antisymmetry lemma);
* `specific_args`: how many arguments of `lem` that are not proofs and not in an instance
  position are something other than one of the theorem's variables: the theorem is `lem` at
  particular terms;
* `repeated_args`: whether one variable of the theorem fills two such positions;
* `specific_levels`: whether `lem`'s universe levels are not distinct universe parameters;
* `unused_hypotheses`: the hypotheses of the theorem (binders whose type is a proposition,
  instance binders included) that the theorem could drop: neither the solution nor the rest of
  the statement (later binders and the conclusion) mentions them;
* `unfolds`: whether the lemma closes the theorem only beyond the search's transparency. For a
  hit of the search it is whether the `relevant` phase found it; for a theorem whose own proof
  applies the lemma (`own_proof`), whether the search, given only that lemma, fails to apply it.

None of this changes an outcome.
-/

open Lean Meta LibrarySearch

namespace DupSearch

/-- Reflexivity: these constants prove an equation, iff or `HEq` between a term and itself,
(`id`) a proposition from itself, or `True`. -/
def reflexiveConstants : List Name :=
  [``rfl, ``Eq.refl, ``Iff.rfl, ``Iff.refl, ``HEq.refl, ``HEq.rfl, ``id, ``trivial, ``True.intro]

/-- Whether a constant is reflexivity: one of `reflexiveConstants`, or a theorem whose
conclusion is a relation between a variable and itself (`le_refl`, `Set.Subset.refl`, a
library's `Equiv.refl`). -/
def isReflexivityLemma (c : Name) : MetaM Bool := do
  if reflexiveConstants.contains c then return true
  let some (.thmInfo info) := (← getEnv).find? c | return false
  forallTelescope info.type fun _ concl => do
    let args := concl.consumeMData.getAppArgs
    let n := args.size
    return n ≥ 2 && args[n - 1]!.isFVar && args[n - 1]! == args[n - 2]!

/-- Constants that build an equation from equations, and stay reflexive when every proof they
are given is: congruence, function extensionality, symmetry and transitivity. -/
def congruenceConstants : List Name :=
  [``congrArg, ``congrFun, ``congr, ``funext, ``Eq.symm, ``Eq.trans, ``Iff.symm, ``Iff.trans,
    ``HEq.symm, ``HEq.trans, ``propext]

/-- Whether a proof is reflexivity: under binders, one of `reflexiveConstants` applied, one of
`congruenceConstants` applied to proofs that are all reflexive, or the identity
(`fun h => h`, a proof of `P → P`). -/
partial def isReflexive (e : Expr) : MetaM Bool := do
  match e.consumeMData with
  | e@(.lam ..) => lambdaTelescope e fun xs b =>
    if xs.size == 1 && b.consumeMData == xs[0]! then pure true else isReflexive b
  | e =>
    let .const c _ := e.getAppFn.consumeMData | return false
    if ← isReflexivityLemma c then return true
    unless congruenceConstants.contains c do return false
    let proofs ← e.getAppArgs.filterM isProof
    return !proofs.isEmpty && (← proofs.allM isReflexive)

/-- Whether a conclusion says nothing about any particular term: past its binders, a variable
applied, or an equation, `HEq` or iff between two distinct variables. -/
def schematic (concl : Expr) : MetaM Bool :=
  forallTelescope concl fun _ c => do
    let c := c.consumeMData
    if c.getAppFn.isFVar then return true
    let vars (a b : Expr) := a.isFVar && b.isFVar && a != b
    if let some (_, a, b) := c.eq? then return vars a b
    if let some (_, a, _, b) := c.heq? then return vars a b
    if let some (a, b) := c.iff? then return vars a b
    return false

/-- Whether the conclusion of `lem`, used as `mod` says, is `schematic`. -/
def isSchematic (lem : Name) (mod : DeclMod) : MetaM Bool := do
  let some info := (← getEnv).find? lem | return false
  forallTelescope info.type fun _ concl => do
    let concl := concl.consumeMData
    match mod, concl.iff? with
    | .mp, some (_, b) => schematic b
    | .mpr, some (a, _) => schematic a
    | _, _ => schematic concl

/-- The facts of the module docs, as a record's `shape`, but `unfolds`, which the caller knows. -/
structure Shape where
  wrappers : Array String := #[]
  headIsLemma : Bool := false
  reflexiveLemma : Bool := false
  reflexiveSideGoals : Nat := 0
  derivedSideGoals : Nat := 0
  schematicLemma : Bool := false
  specificArgs : Nat := 0
  repeatedArgs : Bool := false
  specificLevels : Bool := false
  unusedHypotheses : Array Name := #[]

/-- The record field, with `unfolds`. -/
def Shape.render (s : Shape) (unfolds : Bool) : Json :=
  Json.mkObj [("wrappers", toJson s.wrappers), ("head_is_lemma", s.headIsLemma),
    ("reflexive_lemma", s.reflexiveLemma), ("reflexive_side_goals", s.reflexiveSideGoals),
    ("derived_side_goals", s.derivedSideGoals), ("schematic_lemma", s.schematicLemma),
    ("specific_args", s.specificArgs), ("repeated_args", s.repeatedArgs),
    ("specific_levels", s.specificLevels),
    ("unused_hypotheses", toJson (s.unusedHypotheses.map (·.toString))),
    ("unfolds", unfolds)]

/-- Past the wrappers of the module docs: the lemma's application, the wrappers, and the proofs
the outermost one-way form was given. -/
partial def peelWrappers (e : Expr) (wrappers : Array String := #[]) (extra : Array Expr := #[]) :
    Expr × Array String × Array Expr :=
  let e := e.consumeMData
  let args := e.getAppArgs
  match e.getAppFn.consumeMData with
  | .const c _ =>
    if c == ``Eq.symm && args.size == 4 then peelWrappers args[3]! (wrappers.push "symm") extra
    else if c == ``Iff.symm && args.size == 3 then
      peelWrappers args[2]! (wrappers.push "symm") extra
    else if (c == ``Iff.mp || c == ``Iff.mpr) && args.size ≥ 3 && extra.isEmpty then
      peelWrappers args[2]! (wrappers.push (if c == ``Iff.mp then "mp" else "mpr"))
        (args.extract 3 args.size)
    else (e, wrappers, extra)
  | _ => (e, wrappers, extra)

/-- The shape of `solution`, a proof of `type` (the statement of a theorem, binders and all)
that applies `lem` used as `mod` says. -/
def shapeOf (type solution : Expr) (lem : Name) (mod : DeclMod) : MetaM Shape :=
  forallTelescope type fun xs conclusion => do
    let body ← Core.betaReduce (mkAppN solution xs).headBeta
    let isVar (e : Expr) := e.isFVar && xs.contains e
    let (core, wrappers, extra) := peelWrappers body
    let schematicLemma ← isSchematic lem mod
    let reflexiveLemma ← isReflexivityLemma lem
    let mut s : Shape := { wrappers, reflexiveLemma, schematicLemma }
    -- The hypotheses the theorem could drop. One the statement mentions is needed to state it,
    -- though the solution, by unfolding, may not mention it.
    for h : i in [0:xs.size] do
      let x := xs[i].fvarId!
      if !(← isProp (← x.getType)) || body.containsFVar x || conclusion.containsFVar x then
        continue
      if ← (xs.extract (i + 1)).anyM fun y => return (← inferType y).containsFVar x then
        continue
      s := { s with unusedHypotheses := s.unusedHypotheses.push (← x.getUserName) }
    -- A proof given to the lemma or to its one-way form: a hypothesis, reflexivity, or derived.
    let proofArg (s : Shape) (a : Expr) : MetaM Shape := do
      if isVar a then return s
      if ← isReflexive a then return { s with reflexiveSideGoals := s.reflexiveSideGoals + 1 }
      return { s with derivedSideGoals := s.derivedSideGoals + 1 }
    for a in extra do
      s ← proofArg s a
    let .const c us := core.getAppFn.consumeMData | return s
    unless c == lem do return s
    s := { s with headIsLemma := true }
    let levelParams := us.filterMap fun
      | .param n => some n
      | _ => none
    unless levelParams.length == us.length && levelParams.eraseDups.length == us.length do
      s := { s with specificLevels := true }
    let args := core.getAppArgs
    let info ← getFunInfoNArgs core.getAppFn args.size
    let mut seen : Array Expr := #[]
    for h : i in [0:args.size] do
      let a := args[i]
      if info.paramInfo[i]?.any (·.binderInfo.isInstImplicit) then continue
      if ← isProof a then
        s ← proofArg s a
      else if isVar a then
        if seen.contains a then s := { s with repeatedArgs := true }
        seen := seen.push a
      else
        s := { s with specificArgs := s.specificArgs + 1 }
    return s

end DupSearch

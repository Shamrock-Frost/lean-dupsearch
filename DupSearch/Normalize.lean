import DupSearch.Index

/-!
# Normal forms of statements

Two statements that say the same thing can differ in ways neither the statement index nor the
library search sees: one unfolds a definition the other names, one writes `id x` where the other
writes `x`, one lists its variables in another order. This module puts a statement in a normal
form that removes these differences:

1. **simp.** The statement is simplified with the default simp set and simprocs, with the
   definitions of the library that it mentions unfolded, with the theorem itself (and its
   converse) erased from the simp set, and without discharging the side conditions of
   conditional lemmas. Every rewrite comes with a proof, so the normal form is
   logically equivalent to the statement. The simp lemmas used are recorded: a normal form
   reached through a bookkeeping lemma (`id_eq`, `AlgHom.mem_range`) is a stronger match than
   one reached through a substantive lemma, and a lemma of the library may itself be the
   duplicate. A statement that simp proves outright is reported as such.
2. **binder order and universes** (`canonicalOrder`, `normalLevels`). The binders are put in a canonical order: each as early
   as its dependencies allow, the ready binders ordered by their types (with the binders already
   placed replaced by their positions, and universe names erased, so that no variable or
   universe name matters), ties broken by first occurrence in the conclusion, then in the
   hypotheses. Reordering independent binders does not change what a statement says, so any
   such order is sound: two statements with the same canonical form are the same statement up
   to renaming and reordering, and a tie the order breaks badly can only miss a match. The
   universe levels are then put in Lean's normal form.
3. **instance paths** (`normalHashOf`, `confirmClasses`). The hash erases the arguments in
   instance-implicit positions, since one statement elaborated twice can reach one instance by
   two paths through a class hierarchy; statements that hash alike are then split into classes
   whose normal forms are definitionally equal at `instances` transparency, so that statements
   about genuinely different instances stay apart.

Bound variable names are already irrelevant: Lean refers to bound variables by position, and
`statementHash` erases binder names.
-/

open Lean Meta

namespace DupSearch

/-- A statement's normal form. -/
inductive Normal
  /-- simp proves the statement outright, with these lemmas. -/
  | closed (used : Array Name)
  /-- The normal form, the simp lemmas used to reach it, and whether simp changed anything. -/
  | normal (type : Expr) (used : Array Name) (changed : Bool)
  /-- simp ran out of its budget or failed; the statement is kept as it is. -/
  | failed (why : String)

/-- The name of a simp lemma's origin. -/
def originName (o : Origin) : Name :=
  match o with
  | .decl n .. => n
  | o => o.key

/-- Whether `c` is a definition of the library (`inLibrary` on its module) that unfolding may
open: not an instance, nor a projection. -/
def isLibraryDefinition (env : Environment) (inLibrary : Name → Bool) (c : Name) : Bool :=
  (moduleOf env c).any inLibrary && (env.find? c matches some (.defnInfo _)) &&
    !isInstanceCore env c && !env.isProjectionFn c

/-- Simplify `type`, the statement of `thm`, within `budget` raw heartbeats: the default simp set
and simprocs, plus the unfolding of the definitions of the library (`inLibrary` on their module)
that the statement mentions, minus `thm` itself. -/
def simpNormal (thm : Name) (type : Expr) (inLibrary : Name → Bool) (budget : Nat) :
    MetaM Normal := try
  let env ← getEnv
  let result ← withBudget budget do
    let mut thms ← getSimpTheorems
    for c in type.getUsedConstants do
      if isLibraryDefinition env inLibrary c then thms ← thms.addDeclToUnfold c
    for o in [Origin.decl thm, .decl thm (inv := true)] do
      if thms.isLemma o then thms := thms.eraseCore o
    -- No discharging of side conditions: simp's discharger proves them by recursive simp,
    -- which made normalization five times slower on a measured sample, and left a third of the
    -- statements of a run unfinished within the budget.
    let ctx ← Simp.mkContext { maxDischargeDepth := 0 } #[thms] (← getSimpCongrTheorems)
    let goal ← mkFreshExprMVar type
    let (r, stats) ← simpTarget goal.mvarId! ctx #[← Simp.getSimprocs]
    let used := stats.usedTheorems.toArray.map originName
    match r with
    | none => return Normal.closed used
    | some g =>
      let t ← instantiateMVars (← g.getType)
      return .normal t used (t != type)
  return result.getD (.failed "budget")
catch e =>
  -- simp's own failures (an instance problem that ran out of heartbeats inside it, say) leave
  -- the statement as it is, like a spent budget.
  return .failed ((← e.toMessageData.toString).replace "\n" " ")

/-- The free variables of `es` in order of first occurrence, left to right. -/
partial def occurrenceOrder (es : Array Expr) : Array FVarId :=
  let rec visit (e : Expr) : StateM (Std.HashSet Key × Array FVarId) Unit := do
    if !e.hasFVar || (← get).1.contains ⟨e⟩ then return
    modify fun (seen, order) => (seen.insert ⟨e⟩, order)
    match e with
    | .fvar id => modify fun (seen, order) => (seen, if order.contains id then order else order.push id)
    | .app f a => visit f; visit a
    | .forallE _ t b _ | .lam _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ b | .proj _ _ b => visit b
    | _ => pure ()
  ((es.forM visit).run ({}, #[])).2.2

/-- The binder kinds of the parameters of a constant, as far as its type shows them. -/
def paramInfos (env : Environment) (c : Name) : Array BinderInfo :=
  let rec go : Expr → Array BinderInfo → Array BinderInfo
    | .forallE _ _ b bi, acc => go b (acc.push bi)
    | _, acc => acc
  match env.find? c with
  | some info => go info.type #[]
  | none => #[]

/-- Replace every argument in an instance-implicit position of its function by
`erasedInstance`: two elaborations of one statement can reach one instance by two paths through
a class hierarchy (`NonAssocSemiring.toNonUnitalNonAssocSemiring` and
`NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`, say). Instance binders, the assumptions
themselves, are kept. -/
partial def eraseInstArgs (env : Environment) (e : Expr) : Memo Expr Expr := do
  if let some r := (← get)[(⟨e⟩ : Key)]? then return r
  let r ← match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let infos := match f with
        | .const c _ => paramInfos env c
        | _ => #[]
      let f ← eraseInstArgs env f
      let mut out := #[]
      for h : i in [0:args.size] do
        if infos[i]? == some .instImplicit then out := out.push erasedInstance
        else out := out.push (← eraseInstArgs env args[i])
      pure (mkAppN f out)
    | .forallE n t b bi => pure <| .forallE n (← eraseInstArgs env t) (← eraseInstArgs env b) bi
    | .lam n t b bi => pure <| .lam n (← eraseInstArgs env t) (← eraseInstArgs env b) bi
    | .letE n t v b nonDep =>
      pure <| .letE n (← eraseInstArgs env t) (← eraseInstArgs env v) (← eraseInstArgs env b) nonDep
    | .mdata d b => pure <| .mdata d (← eraseInstArgs env b)
    | .proj s i b => pure <| .proj s i (← eraseInstArgs env b)
    | e => pure e
  modify (·.insert ⟨e⟩ r)
  return r

/-- The key a ready binder is ordered by: its type with the binders already placed replaced by
their positions, binder names, metadata and instance arguments erased, and every universe
parameter renamed to one name, so that no variable or universe name, and no path to an
instance, matters. -/
def binderKey (env : Environment) (type : Expr) (placed : Array Expr) : Expr :=
  let e := (eraseInstArgs env (type.abstract placed)).run' {}
  let e := (norm false e).run' {}
  (renameLevels (fun _ => `u) e).run' {}

/-- Put the binders of a statement in the canonical order (see the module docs). -/
def canonicalOrder (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs body => do
    let env ← getEnv
    let types ← xs.mapM inferType
    let occurrence := occurrenceOrder (#[body] ++ types)
    let rank (x : Expr) : Nat := (occurrence.idxOf? x.fvarId!).getD occurrence.size
    let mut placed : Array Expr := #[]
    let mut remaining : Array (Expr × Expr) := xs.zip types
    while !remaining.isEmpty do
      let pending : Std.HashSet FVarId := remaining.foldl (fun s (x, _) => s.insert x.fvarId!) {}
      let mut best : Option (Nat × Expr × Nat) := none  -- index in `remaining`, key, rank
      for h : i in [0:remaining.size] do
        let (x, t) := remaining[i]
        if t.hasAnyFVar (fun id => id != x.fvarId! && pending.contains id) then continue
        let key := binderKey env t placed
        let better := match best with
          | none => true
          | some (_, k, r) => key.lt k || (key == k && rank x < r)
        if better then best := some (i, key, rank x)
      let some (i, _, _) := best
        | throwError "canonicalOrder: no binder is ready (cyclic dependencies?)"
      placed := placed.push remaining[i]!.1
      remaining := remaining.eraseIdx! i
    mkForallFVars placed body

/-- The universe levels of an expression in Lean's normal form (`Level.normalize`, which
`Level.isEquiv` decides equality by), after the parameters are renamed by first occurrence:
`normalize` orders the arguments of `max` by parameter name, which must not depend on the names a
statement happens to use. Two elaborations of one statement can write one universe as
`succ (max u v)` and as `max (succ u) (succ v)`. -/
def normalLevels (e : Expr) : Expr :=
  (mapLevels Level.normalize (canonicalLevels e)).run' {}

/-- A statement in normal form, past simp: canonical binder order, universe levels in normal
form. -/
def normalForm (type : Expr) : MetaM Expr :=
  return normalLevels (← canonicalOrder type)

/-- The hash of a normal form, with its instance arguments erased. Equal hashes are candidates:
`confirmClasses` checks them, since erasing instance arguments also merges statements about
genuinely different instances. -/
def normalHashOf (env : Environment) (nf : Expr) : String :=
  statementHash ((eraseInstArgs env nf).run' {}) false

/-- The hash of a statement's normal form past simp (`normalForm`, then `normalHashOf`). -/
def normalHash (type : Expr) : MetaM String := do
  return normalHashOf (← getEnv) (← normalForm type)

/-- Split statements whose normal forms hash alike into classes of statements whose normal forms
are definitionally equal at `instances` transparency, so that only the paths to instances, not
the instances, may differ within a class. Each check gets `budget` raw heartbeats; one that runs
out keeps the statements apart. -/
def confirmClasses (members : Array (Name × Expr)) (budget : Nat) : MetaM (Array (Array Name)) := do
  let mut classes : Array (Expr × Array Name) := #[]
  for (n, nf) in members do
    let mut found : Option Nat := none
    for i in [0:classes.size] do
      let same ← withBudget budget <| withTransparency .instances <| withNewMCtxDepth <|
        isDefEq classes[i]!.1 nf
      if same == some true then
        found := some i
        break
    classes := match found with
      | some i => classes.modify i fun (rep, names) => (rep, names.push n)
      | none => classes.push (nf, #[n])
  return classes.map (·.2)

/-- Names as a JSON array, private prefixes dropped. -/
def namesJson (ns : Array Name) : Json :=
  toJson (ns.map fun n => (userName n).toString)

/-- The fields of an index record that report the normal form of `type`, the statement of
`thm`: `normal` (the hash of its normal form, `null` when simp proves the statement),
`normal_status` (`closed`, `changed`, `same`, or `failed` when simp ran out of budget and only
the rest of the normal form was taken) and `normal_used` (the simp lemmas used); and the normal
form itself. -/
def normalFields (thm : Name) (type : Expr) (config : Config) :
    MetaM (List (String × Json) × Option Expr) := do
  let env ← getEnv
  match ← simpNormal thm type config.scope.inLibrary (config.normalizeHeartbeats * 1000) with
  | .closed used =>
    return ([("normal", Json.null), ("normal_status", "closed"), ("normal_used", namesJson used)],
      none)
  | .normal t used changed =>
    let nf ← normalForm t
    return ([("normal", normalHashOf env nf),
      ("normal_status", if changed then "changed" else "same"), ("normal_used", namesJson used)],
      some nf)
  | .failed _ =>
    let nf ← normalForm type
    return ([("normal", normalHashOf env nf), ("normal_status", "failed"),
      ("normal_used", namesJson #[])], some nf)

/-- Write the statement index a configuration file describes: one JSON object per line, a
`start` record, one `theorem` record per theorem with the fields `name`, `module`, `exact`,
`insts` and, when `Config.normalizeHeartbeats` is not `0`, those of `normalFields`; then one
`normal_group` record per normal-form hash shared by several theorems, with `classes`, the
theorems split by `confirmClasses`; and a `done` record. The theorems are those of `DupSearch.libraryTheorems`, private ones left out: a private
theorem is a proof step, which may restate the result it serves. -/
def runIndex (configPath : String) : CoreM Unit := withoutOptions do
  let config ← Config.load configPath
  let env ← getEnv
  let emit ← openOutput config.output
  let theorems := libraryTheorems env config.scope (privates := false)
  emit <| Json.mkObj [("record", "start"), ("config", toJson config),
    ("selected", theorems.size)]
  let mut forms : Std.HashMap String (Array (Name × Expr)) := {}
  for (n, m, val) in theorems do
    let (normal, nf) ← if config.normalizeHeartbeats == 0 then pure ([], none) else
      withoutModifyingEnv <| unlimited <|
        tryCatchRuntimeEx ((normalFields n val.type config).run') fun e => do
          let msg := (← e.toMessageData.toString).replace "\n" " "
          return (([("normal", Json.null), ("normal_status", "error"),
            ("normal_error", toJson msg)] : List (String × Json)), none)
    if let (some nf, some (.str h)) := (nf, normal.lookup "normal") then
      forms := forms.insert h ((forms.getD h #[]).push (n, nf))
    let fields : List (String × Json) := [("record", "theorem"), ("name", toJson n.toString),
      ("module", toJson m.toString), ("exact", statementHash val.type false),
      ("insts", statementHash val.type true)]
    emit <| Json.mkObj (fields ++ normal)
  -- The statements whose normal forms hash alike, split into confirmed classes.
  for (h, members) in forms.toList do
    if members.size < 2 then continue
    let classes ← unlimited <| (confirmClasses members (config.normalizeHeartbeats * 1000)).run'
    emit <| Json.mkObj [("record", "normal_group"), ("normal", h),
      ("classes", toJson (classes.map fun c => c.map (·.toString)))]
  emit <| Json.mkObj [("record", "done")]

end DupSearch

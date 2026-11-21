import Lean

/-!
# What both tools share

The configuration file the driver writes, the scope of a run (which modules form the library
under study), the declaration a generated constant belongs to, and the output file.

The code compiles against every toolchain from Lean 4.27.0 to 4.33.x; it uses only the core
library, so it needs no package of the project under study.
-/

open Lean

namespace DupSearch

/-- The configuration of one process, read from the JSON file the driver writes. -/
structure Config where
  /-- A module belongs to the library when one of these is it or a prefix of it, … -/
  roots : Array String
  /-- … and none of these is. -/
  exclude : Array String
  /-- The file the records are written to, one JSON object per line. -/
  output : String
  /-- The heartbeat budget per theorem, in thousands, as `maxHeartbeats` counts them. -/
  heartbeats : Nat
  /-- The heartbeat budget of each candidate lemma of a theorem, in thousands; a candidate
  that exceeds it is skipped. -/
  candidateHeartbeats : Nat
  /-- Whether to fall back to the lemmas indexed under a wildcard when no candidate applies,
  as `exact?` does. -/
  star : Bool
  /-- The heartbeat budget, in thousands, of simplifying a statement to its normal form
  (`DupSearch/Normalize.lean`); `0` leaves statements as they are. -/
  normalizeHeartbeats : Nat
  /-- Whether to try the lemmas of the library indexed under a wildcard when no candidate closes
  the goal, whatever `star` says: they are few, and the discrimination tree gives no other way
  to a restatement whose conclusion is a bare variable or equation (`x = y`). -/
  libraryStar : Bool
  /-- Whether to try, when no candidate closes the goal and `star` does not hold, the other
  lemmas indexed under a wildcard whose relevance to the theorem is at least `relevance`. -/
  relevantStar : Bool
  /-- The relevance (`DupSearch/Relevance.lean`) from which a candidate that did not close the
  goal is tried again at `default` transparency, with `relevantHeartbeats`, and from which a
  star lemma is tried (`relevantStar`); above `1`, none is. -/
  relevance : Float
  /-- The heartbeat budget, in thousands, of each candidate tried again for its relevance. -/
  relevantHeartbeats : Nat
  /-- The transparency at which candidates are applied and side goals closed: `instances`
  (reducible definitions and instances, as `simp` and `rw` match), `reducible`, or `default`
  (as `exact?`, which unfolds any definition). -/
  transparency : String
  /-- The depth of `solve_by_elim` on the side goals of an applied lemma. -/
  depth : Nat
  /-- This process handles the theorems whose position in name order is `shard` modulo
  `shards`. -/
  shard : Nat
  /-- The number of processes the theorems are dealt to. -/
  shards : Nat
  /-- A file listing the user-facing names of the theorems to search, one per line; all the
  theorems of the library when absent. -/
  only : Option String := none
  /-- The file `DupSearch.runFrequencies` wrote for this process's environment; counted afresh
  when absent. -/
  frequencies : Option String := none
  /-- The gate on candidates: when not `0`, only the candidates whose relevance reaches
  `relevance` (the greater of `Scorer.relevance` and its value with the library's definitions
  unfolded, `Scorer.gateRelevance`) or that are among the `gateTop` most relevant are tried;
  `0` tries every candidate. -/
  gateTop : Nat := 0
  /-- Whether to report, without searching, a theorem whose own proof merely applies another
  theorem to its variables and hypotheses (`restatedLemma`). -/
  ownProof : Bool := false
  /-- The heartbeat budget, in thousands, of trying `rfl`, then `ext` followed by `rfl`, on each
  statement, to label those true by definition; `0` does not try. The label changes no
  outcome. -/
  definitionalHeartbeats : Nat := 0
  /-- The modules, each as its name components, whose theorems this process handles; every
  module of the library when empty. A library whose modules cannot all be imported together is
  split this way among several environments. -/
  modules : Array (Array String)
  deriving FromJson, ToJson

/-- Read and decode a configuration file. -/
def Config.load (path : String) : IO Config := do
  let text ← IO.FS.readFile path
  match (Json.parse text >>= fromJson? : Except String Config) with
  | .ok c =>
    if c.roots.isEmpty then throw <| IO.userError s!"{path}: `roots` is empty"
    if c.shards == 0 || c.shard ≥ c.shards then
      throw <| IO.userError s!"{path}: shard {c.shard} of {c.shards}"
    unless c.transparency ∈ ["instances", "reducible", "default"] do
      throw <| IO.userError s!"{path}: unknown transparency {c.transparency}"
    unless c.relevance ≥ 0 do throw <| IO.userError s!"{path}: relevance {c.relevance}"
    return c
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- A module name from its components. -/
def nameOfParts (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

/-- The transparency a configuration names (checked by `Config.load`). -/
def Config.transparencyMode (c : Config) : Meta.TransparencyMode :=
  match c.transparency with
  | "reducible" => .reducible
  | "default" => .default
  | _ => .instances

/-- The modules whose theorems a process handles. -/
structure Scope where
  /-- A module belongs to the library when one of these is it or a prefix of it, … -/
  roots : Array Name
  /-- … and none of these is. -/
  exclude : Array Name
  /-- The process handles only these modules of the library, when given. -/
  modules : Option NameSet

/-- The scope a configuration names. -/
def Config.scope (c : Config) : Scope :=
  { roots := c.roots.map String.toName, exclude := c.exclude.map String.toName,
    modules := if c.modules.isEmpty then none
      else some (c.modules.foldl (fun s m => s.insert (nameOfParts m)) {}) }

/-- Whether a module belongs to the library. `Name.isPrefixOf` compares whole components, so
`Foo` does not cover `FooTest`. -/
def Scope.inLibrary (s : Scope) (m : Name) : Bool :=
  s.roots.any (·.isPrefixOf m) && !s.exclude.any (·.isPrefixOf m)

/-- Whether the process handles the theorems of a module. -/
def Scope.contains (s : Scope) (m : Name) : Bool :=
  s.inLibrary m && s.modules.all (·.contains m)

/-- The module a constant was declared in, when it is imported. (`EnvironmentHeader.moduleNames`
builds the array of every module's name at each call: a profiled search spent 4% of its time
building it, and more freeing it.) -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return (← env.header.modules[idx.toNat]?).module

/-- Whether `s` is `pre` followed by a nonempty run of digits, as in `eq_1` or `proof_2`. -/
def numbered (pre s : String) : Bool :=
  s.startsWith pre && !(s.drop pre.length).isEmpty && (s.drop pre.length).all Char.isDigit

/-- A name component that Lean or an attribute generates beside a declaration. A theorem
named `eq_of_…` or `ext` by its author is not generated. -/
def generatedComponent (s : String) : Bool :=
  s.startsWith "_" || numbered "eq_" s || numbered "match_" s || numbered "proof_" s ||
    s ∈ ["eq_def", "injEq", "inj", "sizeOf_spec", "noConfusion", "noConfusionType", "rec",
      "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "induct",
      "mutual_induct", "fun_cases", "ctorIdx", "ext_iff", "congr_simp", "splitter"]

/-- The original of a generated name `p.s` that ends in `suffix`, when it exists. -/
def generatedFrom (env : Environment) (p : Name) (s suffix : String) : Option Name :=
  if s.endsWith suffix then
    let base := Name.str p (s.dropEnd suffix.length).toString
    if (env.find? base).isSome then some base else none
  else none

/-- The declaration a constant was generated from: generated components are stripped, a
constructor or projection maps to its structure, a `@[reassoc]` form `f_assoc` to `f`, and the
`ext_iff` that `@[ext]` generates beside a theorem `ext` to that theorem. A constant that was
not generated is its own owner. -/
partial def owner (env : Environment) (n : Name) : Name :=
  match n with
  | .str p s =>
    if s == "ext_iff" && (env.find? (.str p "ext")).isSome then .str p "ext"
    else if generatedComponent s && !p.isAnonymous then owner env p
    else if let some info := env.getProjectionFnInfo? n then owner env info.ctorName.getPrefix
    else if let some (.ctorInfo c) := env.find? n then owner env c.induct
    else if let some base := generatedFrom env p s "_assoc" then base
    else if s.endsWith "ext_iff" then (generatedFrom env p s "_iff").getD n
    else n
  | .num p _ => if p.isAnonymous then n else owner env p
  | .anonymous => n

/-- The name a reader knows a constant by: a private name without its module prefix. -/
def userName (n : Name) : Name :=
  (privateToUserName? n).getD n

/-- The theorems of the library: a theorem declared in a module of the scope, not an internal
detail and not generated beside another declaration; with `privates := false`, not private
either. Sorted by name, so that every process of a run sees them in the same order. -/
def libraryTheorems (env : Environment) (scope : Scope) (privates : Bool) :
    Array (Name × Name × TheoremVal) := Id.run do
  let mut out := #[]
  for (n, info) in env.constants.map₁.toList do
    let .thmInfo val := info | continue
    let some m := moduleOf env n | continue
    unless scope.contains m do continue
    if !privates && isPrivateName n then continue
    if (userName n).isInternalDetail || owner env n != n then continue
    out := out.push (n, m, val)
  return out.qsort (fun a b => Name.lt a.1 b.1)

/-- The kind of a constant, as a word. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- Run `x` with a budget of `budget` raw heartbeats counted from now; `none` when it runs out.
A budget of `0` would mean no limit to Lean, so it counts as run out at once. -/
def withBudget {α : Type} (budget : Nat) (x : Meta.MetaM α) : Meta.MetaM (Option α) := do
  if budget == 0 then return none
  withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
    withCurrHeartbeats <| tryCatchRuntimeEx (some <$> x) fun e =>
      if e.isMaxHeartbeat then pure none else throw e

/-- Run `x` with no heartbeat limit: the steps outside a budgeted step, such as the lookup of
candidates and the rendering of a solution. -/
def unlimited {α : Type} (x : CoreM α) : CoreM α :=
  withReader (fun ctx => { ctx with maxHeartbeats := 0 }) x

/-- Run `x` with no option set. The `lean` frontend that runs the tools sets `Elab.async` and
`internal.cmdlineSnapshots`, which mean nothing to them; but while any option is set, every
trace check (`checkTraceOption`, at each step of `whnf` and `isDefEq`) builds and looks up a
`trace.…` name. -/
def withoutOptions {α : Type} (x : CoreM α) : CoreM α :=
  withReader (fun ctx => { ctx with options := {} }) x

/-- Open the output file and return a function that writes one record as a line and flushes
it, so that a process stopped early keeps what it found. -/
def openOutput (path : String) : IO (Json → IO Unit) := do
  let h ← IO.FS.Handle.mk path .write
  return fun j => do
    h.putStrLn j.compress
    h.flush

end DupSearch

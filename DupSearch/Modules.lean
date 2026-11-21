import DupSearch.Basic

/-!
# The module scan

Read the compiled modules of the library and of everything they import, without building an
environment, and record the import graph and every constant that two modules declare
incompatibly. Two such modules cannot be imported together; the driver uses the graph and the
clashes to split the library among environments that can each be imported, and reports the
clashes, which are duplicates themselves.

The scan reads what a non-`module` file reads when it imports the library (the driver's entry
files are such files): every module transitively imported, and of a `module` file the data of
its `.olean.private` part, which holds all its constants. Two declarations of a name are
compatible as `Lean.finalizeImport` decides it: when one of the two subsumes the other
(`subsumes`, after the private `Lean.subsumesInfo`), as two copies of one theorem statement do;
two definitions of a name never are. The scan records a clash for every pair of declarations of
a name that are not compatible, not only for the pairs `Lean.finalizeImport` would compare in
one import order: it compares each declaration with the one kept so far, so with three or more
declarations of a name, which pairs it compares depends on the modules imported. If `B` and `C`
each restate `A` incompatibly with each other, an environment importing `A` and `B` and one
importing `A` and `C` both load, but one importing `B` and `C` does not. The driver needs every
such pair to plan environments that load. A set of modules whose declarations are pairwise
compatible can be imported in any order.

The output has one JSON object per line: a `start` record, one `module` record per module
reached (`parts`, its name components; `imports`, those of its direct imports; `isModule`), one
`clash` record per incompatible pair of declarations (`constant`, and `modules`, the module of
the declaration visited first and the module of the other, as name components), and a `done`
record.
-/

open Lean

namespace DupSearch

/-- The name components of a module name. -/
def partsOf (n : Name) : Array String :=
  n.components.toArray.map fun
    | .str _ s => s
    | c => toString c

/-- The data of a module as a non-`module` importer loads it: the private part of a `module`
file, the whole `.olean` of any other. -/
def importedData (mod : Name) : IO ModuleData := do
  let file ← findOLean mod
  unless ← file.pathExists do
    throw <| IO.userError s!"object file {file} of module {mod} does not exist"
  let (main, _) ← readModuleData file
  if !main.isModule then return main
  let parts ← readModuleDataParts #[file, OLeanLevel.server.adjustFileName file,
    OLeanLevel.private.adjustFileName file]
  match parts.back? with
  | some (data, _) => return data
  | none => throw <| IO.userError s!"no data in {file}"

/-- `Lean.subsumesInfo` (private to `Lean.Environment`), with `kept` looking up the declarations
kept so far: whether `c₁` may stand for `c₂`. -/
def subsumes (kept : Name → Option ConstantInfo) (c₁ c₂ : ConstantInfo) : Bool :=
  c₁.name == c₂.name && c₁.type == c₂.type && c₁.levelParams == c₂.levelParams &&
    match c₁, c₂ with
    | .thmInfo t₁, .thmInfo t₂ => t₁.all == t₂.all
    | .thmInfo t₁, .axiomInfo a₂ => t₁.all == [a₂.name] && !a₂.isUnsafe
    | .axiomInfo a₁, .axiomInfo a₂ => a₁.isUnsafe == a₂.isUnsafe && isPropCheap a₁.type
    | _, _ => false
where
  /-- Whether `ty = ∀ …, p xs…` with `p : ∀ args…, Prop` for as many `args` as `xs`. -/
  isPropCheap (ty : Expr) : Bool := Id.run do
    let mut ty := ty
    while ty.isForall do
      let .forallE (body := body) .. := ty | return false
      ty := body
    let .const n .. := ty.getAppFn | return false
    let some decl := kept n | return false
    let mut p := decl.type
    for _ in [0:ty.getAppNumArgs] do
      let .forallE (body := body) .. := p | return false
      p := body
    p.isProp

/-- The scan's state: the modules visited in order; for each name, the declaration
`Lean.finalizeImport` would keep so far, with the index of its module (`subsumes` looks other
constants up here); every declaration of each name declared more than once, with the index of
its module; and the clashes found. -/
structure ScanState where
  order : Array (Name × ModuleData) := #[]
  visited : NameSet := {}
  kept : Std.HashMap Name (ConstantInfo × Nat) := {}
  repeated : Std.HashMap Name (Array (ConstantInfo × Nat)) := {}
  clashes : Array (Name × Nat × Nat) := #[]

/-- Visit a module after its imports, depth first, and check each of its constants against every
earlier declaration of its name. -/
partial def visit (mod : Name) : StateT ScanState IO Unit := do
  if (← get).visited.contains mod then return
  modify fun s => { s with visited := s.visited.insert mod }
  let data ← importedData mod
  for i in data.imports do
    visit i.module
  let idx := (← get).order.size
  modify fun s => { s with order := s.order.push (mod, data) }
  for c in data.constants do
    let s ← get
    match s.kept[c.name]? with
    | none => set { s with kept := s.kept.insert c.name (c, idx) }
    | some (prev, prevIdx) =>
      let kept (n : Name) := s.kept[n]?.map (·.1)
      let earlier := s.repeated[c.name]?.getD #[(prev, prevIdx)]
      let mut clashes := s.clashes
      for (d, dIdx) in earlier do
        unless subsumes kept c d || subsumes kept d c do
          clashes := clashes.push (c.name, dIdx, idx)
      set { s with
        kept := if subsumes kept c prev then s.kept.insert c.name (c, idx) else s.kept
        repeated := s.repeated.insert c.name (earlier.push (c, idx))
        clashes }

/-- Scan the library a configuration file names (`modules`, as name components). -/
def runScan (configPath : String) : CoreM Unit := withoutOptions do
  let config ← Config.load configPath
  let emit ← openOutput config.output
  let roots := config.modules.map nameOfParts
  emit <| Json.mkObj [("record", "start"), ("config", toJson config)]
  let (_, s) ← (roots.forM visit).run {}
  for (mod, data) in s.order do
    emit <| Json.mkObj [("record", "module"), ("parts", toJson (partsOf mod)),
      ("imports", toJson (data.imports.map (partsOf ·.module))), ("isModule", data.isModule)]
  for (c, i, j) in s.clashes do
    emit <| Json.mkObj [("record", "clash"), ("constant", toJson c.toString),
      ("modules", toJson #[partsOf s.order[i]!.1, partsOf s.order[j]!.1])]
  emit <| Json.mkObj [("record", "done"), ("modules", toJson s.order.size),
    ("clashes", toJson s.clashes.size)]

end DupSearch

import DupSearch.Normalize

/-!
# The relevance of a candidate lemma to a theorem

The search applies candidates at `instances` transparency, so it misses a lemma that restates a
theorem only up to the unfolding of a definition: `x ∈ separableClosure E K` is
`IsSeparable E x` once membership in `separableClosure` is unfolded. Applying every candidate
at `default` transparency finds such a lemma, but also brings back the costly failures and the
solutions through definitional glue (`SetLike.coe_eq_coe`, `Algebra.algebraMap_self_apply`)
that `instances` transparency removed. What tells the two kinds of lemma apart is their
vocabulary: a restatement is about the same things as the theorem (`FiniteDimensional`,
`CharP`, `Nat.Prime`), while glue is about things every statement mentions.

This is the symbol-based relevance filtering of automated theorem provers (MePo, Meng and
Paulson 2009; SInE, Hoder and Voronkov 2011): a constant is the more telling the fewer
statements of the environment mention it, as the inverse document frequency of information
retrieval weighs a word. Here

* the **vocabulary** of a statement is the set of constants it mentions outside instance
  arguments (`eraseInstArgs`), so that the path to an instance (`Field.toCommRing`, `instHPow`)
  counts for nothing, while the classes a statement assumes (`FiniteDimensional E K`) count;
* the **weight** of a constant is `log ((n + 1) / (k + 1))`, where `n` is the number of
  theorems of the environment and `k` the number whose statement mentions the constant;
* the **relevance** of a lemma to a theorem is the weighted Jaccard similarity of their
  vocabularies: the weight of the constants both mention over the weight of the constants
  either mentions. It is `1` for statements with the same vocabulary and `0` for statements
  that share only constants that every theorem mentions.

The weights are floating-point numbers, so a relevance within rounding error of a threshold
can fall either side of it on another platform's `log`.
-/

open Lean Meta

namespace DupSearch

/-- The vocabulary of a statement: the constants it mentions outside instance arguments. -/
def vocabulary (env : Environment) (type : Expr) : NameSet :=
  let e := (eraseInstArgs env type).run' {}
  e.getUsedConstants.foldl (init := {}) fun s c =>
    if c == erasedInstance.constName! then s else s.insert c

/-- How many theorems of the environment mention each constant (`vocabulary`), and how many
theorems there are. -/
structure Frequencies where
  theorems : Nat
  mentions : Std.HashMap Name Nat

/-- Count the theorems of the environment that mention each constant. Internal details
(auxiliary lemmas, equation lemmas) are left out: they are not statements anyone wrote. -/
def Frequencies.ofEnv (env : Environment) : Frequencies := Id.run do
  let mut theorems := 0
  let mut mentions : Std.HashMap Name Nat := {}
  for (n, info) in env.constants.toList do
    let .thmInfo val := info | continue
    if (userName n).isInternalDetail then continue
    theorems := theorems + 1
    for c in vocabulary env val.type do
      mentions := mentions.insert c (mentions.getD c 0 + 1)
  return { theorems, mentions }

/-- The weight of a constant: `log ((n + 1) / (k + 1))` for `n` theorems of which `k` mention
it. -/
def Frequencies.weight (f : Frequencies) (c : Name) : Float :=
  Float.log ((f.theorems + 1).toFloat / (f.mentions.getD c 0 + 1).toFloat)

/-- The relevance of a statement with vocabulary `b` to one with vocabulary `a`: the weighted
Jaccard similarity of the two, `0` when neither mentions a constant of positive weight. -/
def Frequencies.relevance (f : Frequencies) (a b : NameSet) : Float := Id.run do
  let mut shared := 0.0
  let mut either := 0.0
  for c in a do
    let w := f.weight c
    either := either + w
    if b.contains c then shared := shared + w
  for c in b do
    unless a.contains c do either := either + f.weight c
  return if either > 0 then shared / either else 0

/-- A name as the array of its components, strings and numbers, which reads back exactly
(the escaped string of a name need not, for a private or numbered name). -/
def nameToJson (n : Name) : Json :=
  Json.arr (n.components.toArray.map fun
    | .str _ s => Json.str s
    | .num _ i => toJson i
    | .anonymous => Json.null)

/-- Read a name written by `nameToJson`. -/
def nameFromJson? (j : Json) : Except String Name := do
  let parts ← j.getArr?
  parts.foldlM (init := Name.anonymous) fun n p => match p with
    | .str s => pure (Name.str n s)
    | .num _ => do pure (Name.num n (← fromJson? p))
    | _ => throw s!"not a name component: {p}"

/-- The frequencies as one JSON object. -/
def Frequencies.toJson (f : Frequencies) : Json :=
  Json.mkObj [("theorems", Lean.toJson f.theorems),
    ("mentions", Json.arr (f.mentions.toArray.map fun (c, k) =>
      Json.arr #[nameToJson c, Lean.toJson k]))]

/-- Read frequencies written by `Frequencies.toJson`. -/
def Frequencies.fromJson? (j : Json) : Except String Frequencies := do
  let theorems ← (← j.getObjVal? "theorems").getNat?
  let mut mentions : Std.HashMap Name Nat := {}
  for entry in ← (← j.getObjVal? "mentions").getArr? do
    let c ← nameFromJson? (← entry.getArrVal? 0)
    let k ← (← entry.getArrVal? 1).getNat?
    mentions := mentions.insert c k
  return { theorems, mentions }

/-- Count the frequencies of the environment once, for every search process of the environment
to read: counting walks every statement of the environment, two minutes for a library of 4000
theorems with Mathlib, and processes that do it side by side contend for the memory that holds
them. Writes a `frequencies` record and a `done` record to the configuration's output. -/
def runFrequencies (configPath : String) : CoreM Unit := withoutOptions do
  let config ← Config.load configPath
  let emit ← openOutput config.output
  let t0 ← IO.monoMsNow
  let f := Frequencies.ofEnv (← getEnv)
  emit <| Json.mkObj [("record", "frequencies"), ("frequencies", f.toJson)]
  let t1 ← IO.monoMsNow
  emit <| Json.mkObj [("record", "done"), ("ms", Lean.toJson (t1 - t0))]

/-- What a process needs to score candidates: the frequencies of its environment, which modules
form the library, and the vocabularies computed so far, which recur from one theorem to the
next. -/
structure Scorer where
  frequencies : Frequencies
  inLibrary : Name → Bool
  vocabularies : IO.Ref (Std.HashMap Name NameSet)
  /-- The vocabularies of the bodies of the library's definitions (`isLibraryDefinition`). -/
  bodies : IO.Ref (Std.HashMap Name NameSet)
  /-- The vocabularies of statements with the library's definitions unfolded (`Scorer.unfold`). -/
  unfoldedVocabularies : IO.Ref (Std.HashMap Name NameSet)

/-- A scorer for the current environment, whose library is the modules `inLibrary` accepts, with
the frequencies `runFrequencies` wrote to `path`, or counted afresh. -/
def Scorer.new (inLibrary : Name → Bool) (path : Option String) : CoreM Scorer := do
  let frequencies ← match path with
    | none => pure (Frequencies.ofEnv (← getEnv))
    | some p =>
      let read (line : String) : Except String (Option Frequencies) := do
        let j ← Json.parse line
        if (← j.getObjValAs? String "record") != "frequencies" then return none
        some <$> Frequencies.fromJson? (← j.getObjVal? "frequencies")
      let mut found := none
      for line in (← IO.FS.readFile p).splitOn "\n" do
        if line.isEmpty then continue
        match read line with
        | .ok (some f) => found := some f; break
        | .ok none => pure ()
        | .error e => throwError "{p}: {e}"
      match found with
      | some f => pure f
      | none => throwError "{p}: no frequencies record"
  let vocabularies ← IO.mkRef {}
  let bodies ← IO.mkRef {}
  let unfoldedVocabularies ← IO.mkRef {}
  return { frequencies, inLibrary, vocabularies, bodies, unfoldedVocabularies }

/-- The vocabulary of a constant's statement, empty for a constant not in the environment. -/
def Scorer.vocabularyOf (s : Scorer) (n : Name) : CoreM NameSet := do
  if let some v := (← s.vocabularies.get)[n]? then return v
  let env ← getEnv
  let v := match env.find? n with
    | some info => vocabulary env info.type
    | none => {}
  s.vocabularies.modify (·.insert n v)
  return v

/-- The relevance of a constant's statement to a statement of vocabulary `statement`. -/
def Scorer.relevance (s : Scorer) (statement : NameSet) (n : Name) : CoreM Float :=
  return s.frequencies.relevance statement (← s.vocabularyOf n)

/-- A vocabulary with the library's definitions in it unfolded one level: the vocabulary of each
one's body joins it. A restatement in the library's own terms (`Module.projectiveDimension`)
of a lemma in Mathlib's then shares Mathlib's vocabulary with it. -/
def Scorer.unfold (s : Scorer) (v : NameSet) : CoreM NameSet := do
  let env ← getEnv
  let mut out := v
  for c in v do
    unless isLibraryDefinition env s.inLibrary c do continue
    let body ← match (← s.bodies.get)[c]? with
      | some b => pure b
      | none =>
        let b := match env.find? c with
          | some (.defnInfo d) => vocabulary env d.value
          | _ => {}
        s.bodies.modify (·.insert c b)
        pure b
    out := body.foldl (·.insert ·) out
  return out

/-- The vocabulary of a constant's statement with the library's definitions unfolded. -/
def Scorer.unfoldedVocabularyOf (s : Scorer) (n : Name) : CoreM NameSet := do
  if let some v := (← s.unfoldedVocabularies.get)[n]? then return v
  let v ← s.unfold (← s.vocabularyOf n)
  s.unfoldedVocabularies.modify (·.insert n v)
  return v

/-- The relevance of a constant's statement for the gate of the search: the greater of its
relevance to a statement of vocabulary `statement`, and its relevance once the library's
definitions are unfolded in both (`unfolded` is `statement` unfolded). On a library of
4000 theorems, unfolding raised restatements in the library's own terms from 0.19–0.29 to 0.46–0.87,
while of 278 solutions through definitional glue, 13 reached 0.3 with it and 12 without (the
library's own `ext` lemmas). -/
def Scorer.gateRelevance (s : Scorer) (statement unfolded : NameSet) (n : Name) :
    CoreM Float := do
  let f := s.frequencies
  return max (f.relevance statement (← s.vocabularyOf n))
    (f.relevance unfolded (← s.unfoldedVocabularyOf n))

/-- Items scored against many statements, each by its vocabulary: a statement is compared only
with the items that share a constant of positive weight with it, found through an index from
each constant to the items that mention it. -/
structure Pool (α : Type) where
  items : Array α
  vocabularies : Array NameSet
  /-- The weight of each item's vocabulary. -/
  weights : Array Float
  /-- For each constant of positive weight, the positions of the items that mention it. -/
  mentions : Std.HashMap Name (Array Nat)

/-- The pool of `items`, each with its vocabulary, weighed by `f`. -/
def Pool.new {α : Type} (f : Frequencies) (items : Array (α × NameSet)) : Pool α := Id.run do
  let mut mentions : Std.HashMap Name (Array Nat) := {}
  let mut weights := #[]
  for h : i in [0:items.size] do
    let mut w := 0.0
    for c in items[i].2 do
      let wc := f.weight c
      w := w + wc
      if wc > 0 then mentions := mentions.insert c ((mentions.getD c #[]).push i)
    weights := weights.push w
  return { items := items.map (·.1), vocabularies := items.map (·.2), weights, mentions }

/-- The items whose relevance (`Frequencies.relevance`) to a statement of vocabulary `statement`
is at least `threshold`, with their relevance, most relevant first and ties in pool order.

The weight two vocabularies share is summed through the index, which gives the relevance up to
rounding; every item that comes within `1e-6` of the threshold by that sum, or above it, is
scored again by `Frequencies.relevance`, whose value it is kept by and reported with, so the
result is the one scoring every item would give. An item that shares no constant of positive weight with the
statement has relevance `0`, below any positive threshold. -/
def Pool.relevant {α : Type} (p : Pool α) (f : Frequencies) (statement : NameSet)
    (threshold : Float) : Array (Float × α) := Id.run do
  let mut shared : Std.HashMap Nat Float := {}
  let mut total := 0.0
  for c in statement do
    let w := f.weight c
    total := total + w
    for i in p.mentions.getD c #[] do
      shared := shared.insert i (shared.getD i 0 + w)
  let positions : Array Nat := if threshold > 0 then shared.toArray.map (·.1)
    else Array.range p.items.size
  let mut out : Array (Float × Nat) := #[]
  for i in positions do
    let s := shared.getD i 0
    let either := total + p.weights[i]! - s
    let approx := if either > 0 then s / either else 0
    if approx + 1e-6 < threshold then continue
    let r := f.relevance statement p.vocabularies[i]!
    if r ≥ threshold then out := out.push (r, i)
  let sorted := out.qsort fun (r₁, i₁) (r₂, i₂) => r₁ > r₂ || (r₁ == r₂ && i₁ < i₂)
  return sorted.filterMap fun (r, i) => p.items[i]?.map (r, ·)

end DupSearch

import DupSearch.Basic

/-!
# The statement index

Two hashes of the statement of every public theorem of the library, so that two theorems with
the same statement collide. The `exact` hash is of the type normalized up to the names of its
bound variables and universe parameters and the metadata annotations in it; the `insts` hash
also erases the type's instance-implicit binders, so that two statements that differ only in
the instances they assume hash alike.

`DupSearch.runIndex` (in `DupSearch/Normalize.lean`, since it also records normal forms)
writes the index.
-/

open Lean

namespace DupSearch

/-- The sentinel put in place of an erased instance-implicit binder. -/
def erasedInstance : Expr := .const `DupSearch.erasedInstance []

/-- An expression compared by strict structural equality (`Expr.equal`: binder names and
annotations included), as a key of the caches below. Statements share subterms heavily, so a
pass that does not cache takes time and memory exponential in the size of the statement as
written. -/
structure Key where
  e : Expr

instance : BEq Key := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable Key := ⟨fun a => a.e.hash⟩

/-- A pass over an expression that caches its result on every subterm. -/
abbrev Memo (α : Type) := StateM (Std.HashMap Key α)

/-- Normalize an expression: anonymous binder names and no metadata; with `erase`,
instance-implicit binders are replaced by `erasedInstance`. -/
partial def norm (erase : Bool) (e : Expr) : Memo Expr Expr := do
  if let some r := (← get)[(⟨e⟩ : Key)]? then return r
  let r ← match e with
    | .forallE _ t b bi =>
      if erase && bi == .instImplicit then
        norm erase (b.instantiate1 erasedInstance)
      else
        pure <| .forallE .anonymous (← norm erase t) (← norm erase b) bi
    | .lam _ t b bi => pure <| .lam .anonymous (← norm erase t) (← norm erase b) bi
    | .letE _ t v b nonDep =>
      pure <| .letE .anonymous (← norm erase t) (← norm erase v) (← norm erase b) nonDep
    | .app f a => pure <| .app (← norm erase f) (← norm erase a)
    | .mdata _ e => norm erase e
    | .proj s i e => pure <| .proj s i (← norm erase e)
    | e => pure e
  modify (·.insert ⟨e⟩ r)
  return r

/-- Rename the parameters of a level by `ren`, leaving its structure as it is (`Level.replace`
would also simplify it, as `max 1 (u + 1)` to `u + 1`). -/
def renameLevel (ren : Name → Name) : Level → Level
  | .succ l => .succ (renameLevel ren l)
  | .max l₁ l₂ => .max (renameLevel ren l₁) (renameLevel ren l₂)
  | .imax l₁ l₂ => .imax (renameLevel ren l₁) (renameLevel ren l₂)
  | .param n => .param (ren n)
  | l => l

/-- Apply `f` to every universe level of an expression. -/
partial def mapLevels (f : Level → Level) (e : Expr) : Memo Expr Expr := do
  if let some r := (← get)[(⟨e⟩ : Key)]? then return r
  let r ← match e with
    | .forallE n t b bi => pure <| .forallE n (← mapLevels f t) (← mapLevels f b) bi
    | .lam n t b bi => pure <| .lam n (← mapLevels f t) (← mapLevels f b) bi
    | .letE n t v b nonDep =>
      pure <| .letE n (← mapLevels f t) (← mapLevels f v) (← mapLevels f b) nonDep
    | .app g a => pure <| .app (← mapLevels f g) (← mapLevels f a)
    | .mdata d e => pure <| .mdata d (← mapLevels f e)
    | .proj s i e => pure <| .proj s i (← mapLevels f e)
    | .const n ls => pure <| .const n (ls.map f)
    | .sort l => pure <| .sort (f l)
    | e => pure e
  modify (·.insert ⟨e⟩ r)
  return r

/-- Rename the universe parameters of an expression by `ren`. -/
def renameLevels (ren : Name → Name) (e : Expr) : Memo Expr Expr :=
  mapLevels (renameLevel ren) e

/-- Rename the universe parameters of an expression `u0`, `u1`, … in the order they first occur
in a left-to-right walk (the order `collectLevelParams` records them in). -/
def canonicalLevels (e : Expr) : Expr :=
  let ps := (collectLevelParams {} e).params
  let ren (n : Name) : Name := match ps.idxOf? n with
    | some i => Name.mkSimple s!"u{i}"
    | none => n
  (renameLevels ren e).run' {}

/-- A 64-bit structural hash of a normalized expression; `Expr.hash` keeps only 32 bits and
ignores binder annotations. -/
partial def hash64 (e : Expr) : Memo UInt64 UInt64 := do
  if let some h := (← get)[(⟨e⟩ : Key)]? then return h
  let h ← match e with
    | .bvar i => pure <| mixHash 3 (hash i)
    | .fvar f => pure <| mixHash 5 (hash f)
    | .mvar m => pure <| mixHash 7 (hash m)
    | .sort l => pure <| mixHash 11 (hash l)
    | .const n ls => pure <| mixHash 13 (mixHash (hash n) (hash ls))
    | .app f a => pure <| mixHash 17 (mixHash (← hash64 f) (← hash64 a))
    | .lam _ t b bi => pure <| mixHash 19 (mixHash (hash bi) (mixHash (← hash64 t) (← hash64 b)))
    | .forallE _ t b bi =>
      pure <| mixHash 23 (mixHash (hash bi) (mixHash (← hash64 t) (← hash64 b)))
    | .letE _ t v b _ => pure <| mixHash 29 (mixHash (← hash64 t) (mixHash (← hash64 v) (← hash64 b)))
    | .lit l => pure <| mixHash 31 (hash l)
    | .mdata _ e => pure <| mixHash 37 (← hash64 e)
    | .proj s i e => pure <| mixHash 41 (mixHash (hash s) (mixHash (hash i) (← hash64 e)))
  modify (·.insert ⟨e⟩ h)
  return h

/-- Hexadecimal digits of a hash, zero-padded to 16. -/
def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The hash of a theorem's type, up to bound-variable names and universe parameters, and with
`erase` also up to instance-implicit binders. -/
def statementHash (type : Expr) (erase : Bool) : String :=
  -- Universe parameters are renamed after the erasure, so that a parameter occurring only in an
  -- erased instance takes no number, as in the uncached original of this pass.
  let e := canonicalLevels ((norm erase type).run' {})
  -- Both structural hashes keep their weight: the built-in one ignores binder annotations,
  -- `hash64` does not.
  hex (mixHash ((hash64 e).run' {}) e.hash)

end DupSearch

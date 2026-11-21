/-! Planted duplicates with known answers; `test/test_fixture.py` states what the tools must
report on each declaration. -/

namespace Fixture

/-- Irreducible, so that `apply` cannot see through it to a lemma about `+`. -/
@[irreducible] def double (n : Nat) : Nat := n + n

/-- Restates a core lemma: a trivial hit. -/
theorem add_zero' (n : Nat) : n + 0 = n := Nat.add_zero n

/-- The same, left unproved: a trivial hit on a sorried theorem. -/
theorem add_zero_sorry (n : Nat) : n + 0 = n := sorry

theorem double_ne_zero (n : Nat) (h : 0 < n) : double n ≠ 0 := by
  unfold double; omega

/-- Restates `double_ne_zero` and is proved from it: each closes the other, and the hit on
`double_ne_zero` is marked `uses`. Same statement, so the index groups them. -/
theorem double_ne_zero' (n : Nat) (h : 0 < n) : double n ≠ 0 := double_ne_zero n h

theorem double_eq_zero_iff (n : Nat) : double n = 0 ↔ n = 0 :=
  ⟨fun h => by unfold double at h; omega, fun h => by subst h; unfold double; rfl⟩

/-- One direction of an iff of the library: a hit through `mp`. -/
theorem eq_zero_of_double_eq_zero (n : Nat) (h : double n = 0) : n = 0 :=
  (double_eq_zero_iff n).mp h

/-- A private restatement: searched, but not indexed. -/
private theorem double_ne_zero_private (n : Nat) (h : 0 < n) : double n ≠ 0 :=
  double_ne_zero n h

/-- Not a restatement of anything. -/
theorem double_add (n m : Nat) : double (n + m) = double n + double m := by
  unfold double; omega

/-- `@[ext]` generates `Pt.ext` and `Pt.ext_iff`; the search on `Pt.ext` must not use
`Pt.ext_iff`, and `Pt.ext_iff` is not searched. -/
@[ext] structure Pt where
  x : Nat
  y : Nat

/-- Two statements that differ only in their instance arguments: the index groups them up to
instances only. -/
theorem refl_add {α : Type} [Add α] (a : α) : a = a := rfl

theorem refl_mul {α : Type} [Mul α] (a : α) : a = a := rfl

end Fixture

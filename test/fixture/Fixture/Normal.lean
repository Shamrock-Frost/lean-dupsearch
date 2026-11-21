/-! Statements equal only up to normal form (`DupSearch/Normalize.lean`). The predicates are
opaque, so neither simp nor unfolding can see through them. -/

namespace Fixture

opaque P : Nat → Nat → Prop
opaque Q : Nat → Nat → Prop
opaque R : Nat → Prop
opaque S : Nat → Prop
axiom P_Q (n m : Nat) : P n m → Q m n
axiom R_S (n : Nat) : R n → S n

/-- With `ord_b`, the same statement with the binders in another order, as two `variable` lines
in different orders give: one normal form, two exact hashes. -/
theorem ord_a (n m : Nat) (h : P n m) : Q m n := P_Q n m h

theorem ord_b (m n : Nat) (h : P n m) : Q m n := P_Q n m h

/-- With `idB`, the same statement once simp rewrites `id n` to `n`. The first search pass misses
it (`id` does not unfold at `instances` transparency); the pass on its normal form finds it. -/
theorem idA (n : Nat) (h : R (id n)) : S n := R_S n h

theorem idB (n : Nat) (h : R n) : S n := R_S n h

end Fixture

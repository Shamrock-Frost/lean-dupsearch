import Fixture.Basic
import Fixture.Star

/-! Hits with known readings (`dupsearch.py`, `READINGS`; `DupSearch/Shape.lean`), beside those of
`Basic`: `double_ne_zero'` restates `double_ne_zero` (a duplicate), and `eq_zero_of_double_eq_zero`
is one direction of `double_eq_zero_iff`. -/

namespace Fixture

/-- `double_ne_zero` at `n + 1`: a special case. -/
theorem double_succ_ne_zero (n : Nat) (h : 0 < n + 1) : double (n + 1) ≠ 0 :=
  double_ne_zero (n + 1) h

/-- Its own proof is `Nat.add_zero`, which does not need the hypothesis: a duplicate with an
unneeded hypothesis. -/
theorem add_zero_of_pos (n : Nat) (_h : 0 < n) : n + 0 = n := Nat.add_zero n

/-- Reducible, so that `instances` transparency sees through it, and ignoring its proof. -/
@[reducible] def Tagged (n : Nat) (_ : 0 < n) : Nat := n

/-- Its own proof is `Nat.add_zero`, which does not mention the hypothesis; but the statement
does, so the theorem cannot drop it: a duplicate. -/
theorem tagged_add_zero (n : Nat) (h : 0 < n) : Tagged n h + 0 = n := Nat.add_zero n

/-- `Rel` unfolds to `=`: its own proof is reflexivity, true by unfolding. -/
theorem rel_iff_eq {α : Type} {x y : α} : Rel x y ↔ x = y := Iff.rfl

/-- Not reducible, so that `instances` transparency cannot see `10 < n` in it. -/
def Big (n : Nat) : Prop := 10 < n

/-- Its own proof applies `Nat.lt_succ_of_lt`, which closes it only once `Big` is unfolded and
is not relevant to it: true by unfolding. -/
theorem Big.succ {n : Nat} (h : Big n) : Big (n + 1) := Nat.lt_succ_of_lt h

/-- Reducible, so that `instances` transparency sees through it. -/
@[reducible] def Pt.swap (p : Pt) : Pt := ⟨p.y, p.x⟩

/-- Closed by `Pt.ext` with `rfl` on both side goals: true by unfolding. -/
theorem Pt.swap_mk (a b : Nat) : Pt.swap ⟨a, b⟩ = ⟨b, a⟩ := rfl

end Fixture

import Fixture.Basic

/-! A module the test leaves out of the scope: its theorems are not searched, and a hit on one
of them has origin `excluded`. -/

namespace Fixture

theorem double_add_excluded (n m : Nat) : double (n + m) = double n + double m :=
  double_add n m

end Fixture

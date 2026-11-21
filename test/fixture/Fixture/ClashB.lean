/-! See `ClashA`. -/

namespace Fixture

def clashing : Nat := 2

/-- Searched in the environment of this module. -/
theorem clashB_thm (n : Nat) : 1 * n = n := Nat.one_mul n

end Fixture

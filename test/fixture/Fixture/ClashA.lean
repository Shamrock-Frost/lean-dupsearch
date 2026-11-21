/-! With `ClashB`, two definitions of one name: the modules cannot be imported together, so the
library is split between two environments, and the scan reports the clash. -/

namespace Fixture

def clashing : Nat := 1

/-- Searched in the environment of this module. -/
theorem clashA_thm (n : Nat) : n * 1 = n := Nat.mul_one n

end Fixture

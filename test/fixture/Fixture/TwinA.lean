/-! With `TwinB`, one theorem stated twice: Lean accepts both copies in one environment (each
subsumes the other), so the scan must not report a clash. -/

namespace Fixture

theorem twin : 2 = 2 := rfl

end Fixture

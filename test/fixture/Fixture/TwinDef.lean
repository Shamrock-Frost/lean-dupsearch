/-! `twin` once more, as a definition: it clashes with the theorem of `TwinA` and with that of
`TwinB`. The scan must report both pairs, not only the one `Lean.finalizeImport` would compare
after taking in the twins, or the driver plans an environment importing `TwinDef` with the twin
it did not pair it with, and that environment does not load. -/

namespace Fixture

def twin : Nat := 2

end Fixture

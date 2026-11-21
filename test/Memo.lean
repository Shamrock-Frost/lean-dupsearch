import DupSearch.Index

/-! The cached passes of the statement index must visit each distinct subterm once: statements
share subterms heavily, and a pass that walks them as trees takes exponential time (a `return`
in a match arm once skipped the cache, and the index stalled on a 2414-node statement).
`f x x` nested 64 times has 130 distinct subterms (`x`, `f`, and `f e` and `f e e` at each level)
and a tree of size over 2⁶⁴; each pass must cache exactly the 130 and finish at once. -/

open Lean DupSearch

/-- `f x x` nested `k` times, under a universe-polymorphic constant so that every pass has work
to do: `2k + 2` distinct subterms. -/
def tower : Nat → Expr
  | 0 => .const `x [.param `u]
  | k + 1 => let e := tower k; mkApp2 (.const `f []) e e

#eval show IO Unit from do
  let e := tower 64
  let (n, normCache) := (norm false e).run {}
  let (r, levelCache) := (renameLevels (fun _ => `v) n).run {}
  let (_, hashCache) := (hash64 r).run {}
  for (pass, size) in [("norm", normCache.size), ("renameLevels", levelCache.size),
      ("hash64", hashCache.size)] do
    unless size == 130 do
      throw <| IO.userError s!"{pass} cached {size} subterms, expected 130"
  IO.println "memo ok"

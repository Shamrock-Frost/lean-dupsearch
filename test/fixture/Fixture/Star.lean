/-! Restatements the discrimination tree indexes under a wildcard: the conclusion `x = y` is about
a type that is a variable, so the tree keys it as `Eq * * *`. -/

namespace Fixture

def Rel {α : Type} (x y : α) : Prop := x = y

/-- With `eq_of_rel'`, a restatement only the star lemmas of the library reach. -/
theorem eq_of_rel {α : Type} {x y : α} (h : Rel x y) : x = y := h

theorem eq_of_rel' {α : Type} {x y : α} (h : Rel x y) : x = y := eq_of_rel h

/-- A restatement of a star lemma of core (`Subsingleton.elim`), which only its relevance brings
to the search. -/
theorem subsingleton_eq {α : Type} [Subsingleton α] (x y : α) : x = y := Subsingleton.elim x y

end Fixture

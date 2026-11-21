import DupSearch.Normalize

/-! The normal-form hash must not tell apart two ways of writing one universe: elaborating the
same statement twice in one run of the index gave `Exists.{succ (max u v)}` in one and
`Exists.{max (succ u) (succ v)}` in the other. Nor may it depend on universe names.

Nor may it tell apart two paths to one instance (the same run reached one instance through
`NonAssocSemiring.toNonUnitalNonAssocSemiring` and `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`),
while `confirmClasses` must keep apart statements about genuinely different instances. -/

open Lean Meta DupSearch

/-- `∀ (α : Sort l), α → α` with the universe written as `l`. -/
def statementAt (l : Level) : Expr :=
  .forallE `α (.sort l) (.forallE `a (.bvar 0) (.bvar 1) .default) .default

#eval show MetaM Unit from do
  let u := Level.param `u
  let v := Level.param `v
  let x := Level.param `x
  let y := Level.param `y
  let pairs := [
    ("succ distributes over max", statementAt (.succ (.max u v)),
      statementAt (.max (.succ u) (.succ v))),
    ("universe names do not matter", statementAt (.succ (.max u v)),
      statementAt (.max (.succ y) (.succ x)))]
  for (what, a, b) in pairs do
    unless (← normalHash a) == (← normalHash b) do
      throwError "normalHash tells apart {what}: {a} and {b}"
  if (← normalHash (statementAt u)) == (← normalHash (statementAt (.succ u))) then
    throwError "normalHash merges `Sort u` and `Sort (u + 1)`"
  -- `∀ a b : Nat, a + b = a`, with `+` through the instance `inst`
  let nat := mkConst ``Nat
  let plus (inst : Expr) : Expr :=
    .forallE `a nat (.forallE `b nat
      (mkApp3 (.const ``Eq [1]) nat
        (mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) nat nat nat
          (mkApp2 (.const ``instHAdd [0]) nat inst) (.bvar 1) (.bvar 0))
        (.bvar 1)) .default) .default
  let viaInstance := plus (mkConst ``instAddNat)
  let viaTerm := plus (mkApp2 (.const ``Add.mk [0]) nat (mkConst ``Nat.add))
  let viaMul := plus (mkApp2 (.const ``Add.mk [0]) nat (mkConst ``Nat.mul))
  let hashes ← [viaInstance, viaTerm, viaMul].mapM normalHash
  unless hashes.all (· == hashes[0]!) do
    throwError "normalHash tells apart paths to an instance: {hashes}"
  let forms ← [viaInstance, viaTerm, viaMul].mapM normalForm
  let classes ← confirmClasses #[(`viaInstance, forms[0]!), (`viaTerm, forms[1]!),
    (`viaMul, forms[2]!)] (20000 * 1000)
  unless classes == #[#[`viaInstance, `viaTerm], #[`viaMul]] do
    throwError "confirmClasses gave {classes}"
  IO.println "normal ok"

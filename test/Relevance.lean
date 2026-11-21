import DupSearch.Relevance

/-! The frequencies a separate process counts must read back exactly: names whose escaped string
does not (private names, numbered components, components that need `«»`), and the counts. A pool
must find the items scoring them all would. -/

open Lean Meta DupSearch

theorem relevanceTestLemma : True := trivial

#eval show MetaM Unit from do
  let env ← getEnv
  let names : List Name := [`Nat.add, Name.mkNum `foo 3, `«odd-name».x, .str .anonymous "a.b",
    mkPrivateName env `secret, .anonymous]
  for n in names do
    match nameFromJson? (nameToJson n) with
    | .ok m => unless m == n do throwError "name {n} reads back as {m}"
    | .error e => throwError "name {n}: {e}"
  let f := Frequencies.ofEnv env
  match Json.parse (f.toJson.compress) >>= Frequencies.fromJson? with
  | .error e => throwError "frequencies: {e}"
  | .ok g =>
    unless g.theorems == f.theorems && g.mentions.size == f.mentions.size &&
        f.mentions.toList.all (fun (c, k) => g.mentions[c]? == some k) do
      throwError "frequencies do not read back"
  -- A statement shares all its vocabulary with itself and none with an empty one.
  let v := vocabulary env (← getConstInfo ``Nat.add_comm).type
  unless f.relevance v v == 1 && f.relevance v {} == 0 do
    throwError "relevance {f.relevance v v} and {f.relevance v {}}"
  -- A pool gives what scoring every item gives, in the same order.
  let thms := env.constants.toList.filterMap fun (n, i) =>
    if i matches .thmInfo _ && !n.isInternalDetail then some (n, vocabulary env i.type) else none
  let thms := (thms.toArray.qsort (·.1.quickLt ·.1)).extract 0 3000
  let pool := Pool.new f thms
  for h : k in [0:thms.size] do
    unless k % 60 == 0 do continue
    let st := thms[k].2
    for t in [0.0, 0.1, 0.3, 0.7] do
      let naive := (Array.range thms.size).filterMap (fun i =>
        let r := f.relevance st thms[i]!.2
        if r ≥ t then some (r, i) else none)
        |>.qsort (fun (r₁, i₁) (r₂, i₂) => r₁ > r₂ || (r₁ == r₂ && i₁ < i₂))
        |>.map fun (r, i) => (r, thms[i]!.1)
      let got := pool.relevant f st t
      unless got.size == naive.size && (got.zip naive).all (fun ((r, n), (r', n')) => r == r' && n == n') do
        throwError "pool at {t} for {thms[k].1}: {got.size} items, scoring all gives {naive.size}"
  IO.println "relevance ok"

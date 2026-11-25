import Solution

/-!
Compares `Challenge/Statement.lean` (Mathlib only, proofs `sorry`) with `Solution.lean` (the same definitions and
statements, with proofs). The two files declare the same names, so they cannot be imported together. This file
imports `Solution` and reads the compiled `Challenge/Statement.olean` without importing it.

For every declaration of the statement file it checks: `Solution` has a declaration of the same name and kind; the
types are the same term, up to the names of the universe parameters; for definitions the values are the same term too;
for the structure `IsRankFunction` the inductive type, its constructor and its recursor agree. Theorems are compared by
their types only (their values are `sorry` in the statement file). It also checks that the statement file imports only
`Mathlib` (and `Init`), and that the three main results are theorems in `Solution`.

Run after `lake build Challenge`.
-/

open Lean Meta

run_meta do
  let env ← getEnv
  let (md, _) ← readModuleData (← findOLean `Challenge.Statement)
  for imp in md.imports do
    unless imp.module == `Init || imp.module == `Mathlib do
      throwError "the statement file imports {imp.module}"
  let mut n := 0
  for c in md.constants do
    let some y := env.find? c.name
      | throwError "{c.name} is in the statement file but not in Solution"
    unless c.levelParams.length == y.levelParams.length do
      throwError "{c.name}: the numbers of universe parameters differ"
    -- the names of the universe parameters can differ; rename those of the statement file
    let ren : Expr → Expr := fun e => e.instantiateLevelParams c.levelParams (y.levelParams.map mkLevelParam)
    unless ren c.type == y.type do throwError "{c.name}: the types differ"
    match c, y with
    | .thmInfo _, .thmInfo _ => pure ()
    | .defnInfo a, .defnInfo b =>
      unless ren a.value == b.value do throwError "{c.name}: the values differ"
    | .inductInfo a, .inductInfo b =>
      unless a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all &&
          a.ctors == b.ctors && a.isRec == b.isRec && a.isReflexive == b.isReflexive do
        throwError "{c.name}: the inductive types differ"
    | .ctorInfo a, .ctorInfo b =>
      unless a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams &&
          a.numFields == b.numFields do
        throwError "{c.name}: the constructors differ"
    | .recInfo a, .recInfo b =>
      unless a.numParams == b.numParams && a.numIndices == b.numIndices && a.numMotives == b.numMotives &&
          a.numMinors == b.numMinors && a.k == b.k && a.rules.length == b.rules.length &&
          (a.rules.zip b.rules).all (fun p => p.1.ctor == p.2.ctor && p.1.nfields == p.2.nfields &&
            ren p.1.rhs == p.2.rhs) do
        throwError "{c.name}: the recursors differ"
    | _, _ => throwError "{c.name}: the kinds of declaration differ, or it is an axiom, opaque or quotient"
    n := n + 1
  for t in [`RankRingsChallenge.elek_countable, `RankRingsChallenge.elek_complex,
      `RankRingsChallenge.finite_form] do
    unless md.constNames.contains t do throwError "{t} is not in the statement file"
    unless (env.find? t matches some (.thmInfo _)) do throwError "{t} is not a theorem in Solution"
  logInfo m!"all {n} declarations of Challenge.Statement are equal to those of Solution"

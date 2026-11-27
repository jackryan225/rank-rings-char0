# Regular rank rings over ℚ that do not map into limits of matrix rings

This repository contains Lean 4 proofs of one theorem and its finite form.
Published on 25 November 2026 (preprint, not yet peer reviewed).

Orchestrated and formally verified by Jack Ryan in collaboration with Claude Opus 5.5, Claude Fable 5.2, GPT-6.2 Astra, and Gemini 4 Neon.

**The claim.** There is a countable von Neumann regular ℚ-algebra with a rank function that has no unital ring
homomorphism into any rank ultraproduct of matrix rings over fields of characteristic 0.

This gives a negative answer to a question of G. Elek in one reading: "countable regular rank ℚ-algebra". Other
readings of the question stay open. The section "What is not claimed" lists them.

**Addendum of 25 November 2026 (paper proof, not checked in Lean).** The same ring has no unital ring homomorphism
into the ring of operators affiliated with any nonzero finite von Neumann algebra, and none into any unital
C*-algebra with a tracial state. See the section "Addendum: finite von Neumann algebras" and the file `VN.md`.

## Definitions

- A ring is *unital* if it has a 1. All rings here are unital. A ring homomorphism is *unital* if it maps 1 to 1.
- A ring `S` is *von Neumann regular* (here: *regular*) if for each `a` in `S` there is a `b` in `S` with `aba = a`.
- A *rank function* on a ring `S` is a map `rk` from `S` to the interval `[0, 1]` with these properties:
  `rk(1) = 1`; `rk(a) = 0` only if `a = 0`; `rk(a + b) ≤ rk(a) + rk(b)`; `rk(ab) ≤ rk(a)` and `rk(ab) ≤ rk(b)`;
  `rk(e + f) = rk(e) + rk(f)` for idempotents `e`, `f` with `ef = fe = 0`.
  For an `N × N` matrix `a` over a field, `rank(a) / N` is an example.
- A *regular rank ring* is a regular ring with a rank function. A *regular rank ℚ-algebra* is a regular rank ring
  that is also an algebra over the field ℚ of rational numbers.
- *Rank ultraproduct of matrix rings.* Take a set `I`, an ultrafilter `ω` on `I`, positive integers `d_i` and
  fields `F_i`. Let `J` be the set of sequences `(a_i)` in the product ring `∏ M_{d_i}(F_i)` with
  `rank(a_i) / d_i → 0` along `ω`. Then `J` is a two-sided ideal. The rank ultraproduct is the quotient ring
  `∏ M_{d_i}(F_i) / J`.

## The question

G. Elek, *Connes embeddings and von Neumann regular closures of group algebras*, Trans. Amer. Math. Soc. 365
(2013), 3019-3039, arXiv:1006.5378, Section 1.2. He takes `I = ℕ`, a nonprincipal ultrafilter `ω`, sizes
`d_1 < d_2 < ...` and `F_i = ℂ` for all `i`. He calls this rank ultraproduct `M^alg_ν`. He calls the following "a
purely algebraic version of the Connes Embedding Problem" and asks "whether any countable dimensional regular rank
ring embeds to some M^alg_ν".

## What Lean checks

`Challenge/Statement.lean` imports Mathlib only. It defines every notion above and states three theorems.
`Solution.lean` has the same text with proofs.

1. **`RankRingsChallenge.elek_countable`.** There is a countable regular rank ℚ-algebra `S` with this property.
   For every index type `I`, every ultrafilter `ω` on `I` (principal ones too), all positive sizes `d_i` and all
   fields `F_i` of characteristic 0, there is no unital ring homomorphism from `S` to the rank ultraproduct. The
   fields can change with `i`. Elek's rings `M^alg_ν` are among these targets.
2. **`RankRingsChallenge.elek_complex`.** The same for a regular rank ℂ-algebra. Lean states nothing about its
   dimension over ℂ.
3. **`RankRingsChallenge.finite_form`.** There are finitely many generators, finitely many relations with integer
   coefficients, and a number `ε > 0`. The relations hold exactly in a countable regular rank ℚ-algebra. For each
   `N ≥ 1` and each choice of complex `N × N` matrices for the generators, some relation gives a matrix of rank
   larger than `εN`.

`RankRings/` has the proofs and these further theorems:

- **Finite form over every field of characteristic 0.** `RankRings.finite_form_char0` is statement 3 with every
  field `F` of characteristic 0 (a field in Lean's universe `Type`) in place of ℂ, with one `ε` for all fields.
  `RankRings.finite_form_paper` is the same with the relations of `B_7` exactly as written below.
- **The characteristic contrast.** `RankRings.char_contrast` and `RankRings.finite_form_modL`: the same finite set
  of integer relations has no approximate solution by `N × N` matrices over ℂ, for any `N`, up to rank `εN`. It has
  exact solutions by `N × N` matrices over the field `𝔽_7` with 7 elements, for every `N = 3^(3k+1)`.
  `RankRings.exists_config_modL` gives exact solutions over `𝔽_ℓ` for every prime `ℓ`.
- The steps of the proof: `RankRings.ineq_C` (the inequality below, over ℂ), `RankRings.exotic_RR` (the
  configuration in the `ℓ`-adic rank ring), `RankRings.Gen.no_config` (no configuration in a rank ultraproduct over
  fields of characteristic 0), `RankRings.rr_regular` (the `ℓ`-adic rank ring is regular).

**Stable finiteness (paper argument, not in Lean).** `S` is stably finite: `M_n(S)` is directly finite for every
`n`. The ring `M_n` of the `ℓ`-adic rank ring is again an `ℓ`-adic rank ring, with `n`-fold larger matrices, so it
has a faithful rank function, and a ring with a faithful rank function is directly finite. The rank function of
`S` extends to a faithful Sylvester matrix rank function (Goodearl, *von Neumann Regular Rings*, Chapter 16). In
particular, `S` (and the finitely generated complex subalgebra inside `elek_complex`) is a stably finite algebra that
is not linear sofic while still admitting a faithful Sylvester rank function, contrasting with Greenfeld's stably
finite non-linearly-sofic algebras (B. Greenfeld, *Math. Proc. Cambridge Philos. Soc.* 175 (2023), 319-325,
arXiv:2210.11650; see "Earlier work" below), which admit no faithful Sylvester rank function.

## The relations `B_ℓ`

Let `ℓ` be a prime (the obstruction in characteristic 0 uses `ℓ ≥ 7`, specifically `ℓ = 7`; the exact solutions over `𝔽_ℓ` hold for every prime `ℓ`). Let `P` be the set of points and `L` the set of lines of the projective plane over `𝔽_ℓ`.
Fix a bijection `σ : P → L` **without fixed point**: `p` does not lie on `σ(p)`, for every point `p`. Such a `σ`
exists by Hall's theorem. Let `E` be the set of pairs `(p, p')` of points with `p` on the line `σ(p')`.

`B_ℓ` is the ring with generators `f_p` (`p` in `P`) and `x_{e,i}`, `y_{e,i}` (`e` in `E`, `i = 0, 1, 2`) and
these relations, for `e = (p, p')` in `E`:

```
f_p f_p = f_p,     f_p x_{e,i} = x_{e,i},     f_{p'} x_{e,i} = 0,     y_{e,0} x_{e,0} + y_{e,1} x_{e,1} + y_{e,2} x_{e,2} = 1.
```

The condition on `σ` is necessary. If `p` lies on `σ(p)`, then `(p, p)` is in `E`. The relations then give
`x_{e,i} = 0` and `1 = 0`.

In a regular rank ring the relations force `rk(f_p S ∩ (1 - f_{p'}) S) ≥ 1/3` for every `(p, p')` in `E`. The
proof in `RankRings/` (`finite_form`, `char_contrast`) uses an equivalent form with one more generator `g_e` per
edge. `finite_form_paper` uses the relations above literally, for `ℓ = 7`.

## The mechanism in five lines

1. Over a field of characteristic 0, idempotent `N × N` matrices `f_p` satisfy
   `Σ_{(p,p') in E} dim(im f_p ∩ ker f_{p'}) ≤ (q+1) n N (1 + √q/(q+1)) / 4` for a plane of order `q` with `n` points.
   The proof changes the inner product so that the projections balance, and then uses Cauchy-Schwarz on the incidences.
2. Over a field with an `ℓ`-adic absolute value, sequences of matrices modulo the sequences of small rank "up to small
   entries" form a regular rank ring. In this ring, entries divisible by high powers of `ℓ` count as zero.
3. Tensor powers of integer lifts of flags of the plane over `𝔽_ℓ` give idempotents in that ring that satisfy the
   relations of `B_ℓ`. So each intersection in line 1 has rank at least 1/3.
4. For `ℓ = 7` this breaks the bound of line 1: `1/3 > (1 + √7/8)/4 = 0.3327...`.
5. A unital map into a rank ultraproduct over fields of characteristic 0 would give approximate solutions by matrices
   at some coordinate, against line 1. The countable ring is generated by the relations, ℚ and quasi-inverses.

## Addendum: finite von Neumann algebras

**Paper proof. Not checked in Lean. Not refereed.** Added on 25 November 2026. The full statements and the proof are
in `VN.md`.

Let `M` be a finite von Neumann algebra and `U(M)` its ring of affiliated operators (closed, densely defined). With a
faithful normal tracial state `τ`, the ring `U(M)` is a regular rank ring: the rank of an operator is the trace of
its range projection.

- **The inequality.** Line 1 of the mechanism holds in `U(M)` for all idempotents `f_p`, bounded or not:
  `Σ_{(p,p') in E} dim_τ(f_p U(M) ∩ (1 - f_{p'}) U(M)) ≤ n (q + 1 + √q) / 4`. For `M = M_N(ℂ)` this is line 1.
- **No homomorphism.** A ring that contains a configuration (the Lean structure `RankRings.Config`) has no unital ring
  homomorphism into `U(M)`, for every nonzero finite von Neumann algebra `M`. Lean proves that the ring `S` behind
  `elek_countable` contains a configuration (`RankRings.main_core`). So `S` has no unital ring homomorphism into any
  `U(M)`.
- **C\*-algebras.** `S` has no unital ring homomorphism into a unital C*-algebra that has a tracial state.
- **Maps that are not unital.** `S` has no nonzero ring homomorphism into any `U(M)`.

The proof changes the inner product as in line 1. The potential is the trace of a logarithm, and the infimum need not
be attained. An approximation by bounded idempotents gives the case of unbounded idempotents.

What this addendum does **not** give:

- It answers none of the three open readings of Elek's question that the next section lists.
- Neither this addendum nor the Lean theorem is derived from the other here: a rank ultraproduct of matrix rings is
  not presented as a ring `U(M)`, and `U(M)` is not assumed to embed into a rank ultraproduct of matrix rings.
- It says nothing about groups. For every group `G`, the group algebra `ℂ[G]` lies in `U(L(G))`, where the inequality
  holds. So it gives nothing for sofic or hyperlinear groups or for the Connes embedding problem.
- Finite AW*-algebras that are not von Neumann algebras are not treated.

Checks: three write-ups of the proof by two model families (Claude; GPT-6.2 Astra, one of its two from the bare
statement without a proof), and line-by-line readings by Claude and by GPT-6.2 Sol. The readings found no false step.
They found gaps in the writing, which `VN.md` fills. Gemini 4 Neon has not checked the addendum at this date.

## What is not claimed

These readings of Elek's question are **not** answered here:

- **ℂ-algebras of countable dimension over ℂ, with ℂ-linear embeddings.** The ring of statement 1 is a ℚ-algebra.
  The ℂ-algebra of statement 2 is not shown to have countable dimension over ℂ. In a regular rank ℂ-algebra of
  countable dimension, every element is a root of a nonzero polynomial over ℂ: `a - λ` is invertible for all but
  countably many `λ`, and uncountably many inverses `(a - λ)^(-1)` in a space of countable dimension are linearly
  dependent. We do not know if such a ring can fail to embed.
- **`*`-regular rings and maps that keep the involution.** Elek's rings `M^alg_ν` have an involution. Our rings have
  none in Lean. That version is not treated here.
- **Targets over fields of positive characteristic.** Lean needs characteristic 0 at every coordinate. Rank
  ultraproducts over the fields `𝔽_{p_i}` with `p_i → ∞` are also ℚ-algebras. Our argument does not exclude them.

Without the words "ℚ-algebra", the reading "countable regular rank ring" has a trivial answer. The field `𝔽_2` is a
countable regular rank ring, and it has no unital map into a ring that contains ℚ. That is why the claim says
ℚ-algebra.

Also not claimed:

- **Maps that are not unital.** Lean excludes unital maps. A map that sends 1 to an idempotent `e ≠ 0` is a unital map
  into the corner `eMe`. That corner is again a rank ultraproduct of matrix rings over the same fields. So no nonzero
  ring homomorphism exists. This is a paper argument. It is not in Lean.
- **Elek's second question** (arXiv:1512.03959, Question 1, finite dimensional algebras over finite fields).
- **Groups.** Nothing about sofic, linear sofic or hyperlinear groups. Nothing about the Connes embedding problem for
  von Neumann algebras. The addendum on finite von Neumann algebras does not change this.
- **More structure of `S`.** Lean does not state that `S` is simple, or that its rank function is unique.

### Small differences between Lean and Elek's text

- Elek's list of axioms for a rank function does not contain `rk(1) = 1`. Lean contains it. This makes the existence
  statements stronger.
- Lean allows every ultrafilter on every index type, all positive sizes and all fields of characteristic 0. This
  contains Elek's targets.
- Elek does not define "embeds". Lean excludes every unital ring homomorphism. Such a map need not be injective,
  rank preserving or ℂ-linear.
- Lean forms the quotient by the ring congruence that the relation "`a - b` is in `J`" generates. Because `J` is an
  ideal, this is the quotient by `J`. `Check/Sanity.lean` proves this (`quotient_eq`).
- Lean asks for `d_i > 0` and characteristic 0 at every `i`. A change of the coordinates outside a set of `ω` does
  not change the quotient.

## The main statement in Lean

```lean
theorem elek_countable : ∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
    ∃ rk : S → ℝ, IsRankFunction rk ∧
      ∀ (I : Type) (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
        [∀ i, CharZero (F i)], (∀ i, 0 < d i) → IsEmpty (S →+* RankUltraproduct ω d F)
```

`RankUltraproduct ω d F` is the quotient of `∀ i, Matrix (Fin (d i)) (Fin (d i)) (F i)` by `ringConGen` of the
relation `Filter.Tendsto (fun i => ((a i - b i).rank : ℝ) / d i) ω (nhds 0)`.

## Earlier work

- G. Elek, cited above: the question.
- G. Elek, E. Szabó, *Sofic groups and direct finiteness*, J. Algebra 280 (2004), 426-434, arXiv:math/0305440. Rank
  ultraproducts of matrix rings.
- K. R. Goodearl, *von Neumann Regular Rings*, second edition, Krieger, 1991, Chapter 16. Rank functions.
- G. Arzhantseva, L. Păunescu, *Linear sofic groups and algebras*, Trans. Amer. Math. Soc. 369 (2017), 2285-2310,
  arXiv:1212.6780. A countably generated algebra over a field `F` is *linear sofic* if it has an injective morphism
  into a rank ultraproduct of the rings `M_{n_k}(F)`, unital if the algebra is unital (Definition 4.2). In their
  terms, `S` is not linear sofic over ℚ. Over ℂ, the ℂ-subalgebra generated by the configuration in the ring of
  `elek_complex` is finitely generated and not linear sofic. Neither has a unital map into such an ultraproduct at
  all; their Proposition 11.2 calls this "no almost finite dimensional representations". (The step to ℂ and the
  identification of the targets are paper arguments of a few lines, not in Lean.)
- B. Greenfeld, *Stable finiteness does not imply linear soficity*, Math. Proc. Cambridge Philos. Soc. 175 (2023),
  319-325, arXiv:2210.11650. Finitely generated algebras over every field that are stably finite and not linear
  sofic. His Lemma 2.1 forces every Sylvester rank function on his examples to vanish on a nonzero element (a
  three-line deduction; the paper does not state it). So his examples have no faithful Sylvester rank function and
  do not embed into a regular rank ring. They do have Sylvester rank functions that are not faithful. Our ring is
  also stably finite and not linear sofic, and it is a regular ring with a faithful rank function. Our result is for
  characteristic 0 only.
- M. Lupini, arXiv:1111.0729, answers a different question of Elek.
- F. Barthe, Invent. Math. 134 (1998), 335-361; Z. Dvir, G. Hu, arXiv:1412.0795; B. Barak, Z. Dvir, A. Wigderson,
  A. Yehudayoff, arXiv:1009.4375. Changes of inner product and matrix scaling for rank bounds in characteristic 0.
  The Lean proof of line 1 uses its own potential.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, *MIP\* = RE*, arXiv:2001.04383. The negative answer to the
  Connes embedding problem for von Neumann algebras.

`NOVELTY.md` lists the searches for an earlier answer to Elek's question. We found none. A search cannot prove that
there is none. If you know an earlier answer, please open an issue.

## How to check it

```
lake exe cache get                                    # compiled Mathlib
lake build                                            # the proofs (RankRings, Solution)
lake env lean Check/Axioms.lean                       # each result: propext, Classical.choice, Quot.sound
lake build Challenge && lake env lean Check/SameStatement.lean
lake env lean Check/Sanity.lean                       # the definitions admit maps from ℚ, ℂ and M_2(ℚ)
lake env leanchecker RankRings Solution               # replays the proofs in the kernel checker
```

Lean 4.35.0 (`lean-toolchain`). Mathlib commit `56a0058` (`lake-manifest.json`). The workflow
`.github/workflows/check.yml` runs the first five steps on each push.

`Challenge/Statement.lean` and `Solution.lean` declare the same names, so one Lean file cannot import both.
`Check/SameStatement.lean` imports `Solution` and reads the compiled statement file. It checks that each declaration
of the statement file is the same term as the declaration of the same name in `Solution`: types, values of
definitions, and the structure `IsRankFunction`. Theorems are compared by their types. It also checks that the
statement file imports Mathlib only. `Check/ChallengeView.lean` and `Check/SolutionView.lean` print the definitions
and the three statements in full; the two outputs must be equal.

`Check/Sanity.lean` shows that the statements are not true for a trivial reason. With positive sizes the rank
ultraproduct is not the zero ring. The rings ℚ, ℂ and `M_2(ℚ)` are regular rank rings that do map unitally into
such ultraproducts.

### Results of the checks

On 2026-11-25 these files were built from an empty folder (Mathlib from `lake exe cache get`). Results:

- `lake build`: success (8948 jobs). No `sorry`, `native_decide` or `axiom` in `RankRings/`, `RankRings.lean`,
  `Solution.lean`.
- `Check/Axioms.lean`: all 21 results depend only on `propext`, `Classical.choice`, `Quot.sound`.
- `Check/SameStatement.lean`: all 20 declarations of `Challenge/Statement.lean` are equal to those of `Solution.lean`.
  The `pp.all` outputs of `Check/ChallengeView.lean` and `Check/SolutionView.lean` are byte-identical.
- `Check/Sanity.lean`: compiles; its 5 results depend only on `propext`, `Classical.choice`, `Quot.sound`. (A first run
  showed a missing `Decidable` instance in `field_example`; the file was fixed with the line `open Classical in`
  and run again in the same folder.)
- `leanchecker` (the kernel replay checker of Lean): 23 modules (`RankRings`, its 21 modules, `Solution`), success.
- `lean4lean` (an independent kernel written in Lean): the export of `elek_countable`, `elek_complex`, `finite_form`
  with all dependencies (53,498 theorems; axioms `Classical.choice`, `Quot.sound`, `propext`): 68,066 declarations
  checked, success.

Short logs are in `logs/`.

| File | Content |
|---|---|
| `RankRings/LogDet.lean`, `RankRings/Descent.lean` | log-determinant inequalities; the balanced inner product |
| `RankRings/Plane.lean`, `RankRings/Ineq.lean` | the estimate on the projective plane; the inequality (`ineq_C`) |
| `RankRings/SRank.lean`, `RankRings/Smith.lean` | rank up to small entries; the Smith normal form over an ultrametric field |
| `RankRings/RankRing.lean`, `RankRings/RankFn.lean` | the `ℓ`-adic rank ring, its rank function, regularity |
| `RankRings/Words.lean`, `RankRings/WordsBlock.lean`, `RankRings/Geom.lean` | tensor powers on words; adapted bases; Hall's theorem for `σ` |
| `RankRings/Exotic.lean`, `RankRings/ExoticS.lean` | the configuration in the `ℓ`-adic rank ring |
| `RankRings/NoHom.lean`, `RankRings/NoHomF.lean` | no configuration in rank ultraproducts over ℂ and over fields of characteristic 0 |
| `RankRings/CAlg.lean` | the algebraic closure of the 7-adic numbers is isomorphic to ℂ as a ring |
| `RankRings/Main.lean`, `RankRings/Final.lean`, `RankRings/FiniteForm.lean` | the countable ring; the ℂ-algebra; the finite form over ℂ |
| `RankRings/FiniteFormF.lean` | the finite form over every field of characteristic 0; the relations of `B_7` literally |
| `RankRings/ModL.lean` | exact solutions over `𝔽_ℓ`; the characteristic contrast |
| `Solution.lean`, `Challenge/Statement.lean` | the three statements, with and without proofs |
| `Check/*.lean` | the checks above |
| `logs/` | short logs of the checks of 2026-11-25 |
| `VN.md` | the addendum on finite von Neumann algebras: statements and paper proof (not checked in Lean) |

## Credit

Orchestrated and formally verified by Jack Ryan in collaboration with Claude Opus 5.5, Claude Fable 5.2, GPT-6.2 Astra, and Gemini 4 Neon. The main theorems are formalized in Lean 4 with Mathlib (CI passing; replayed with `leanchecker` and checked by `lean4lean` across 68,066 declarations).

The blind check got the statements without the proofs. It proved the inequality of line 1 by its own route, and the
step from that inequality to the finite form. It did not decide the existence of the configuration in the `ℓ`-adic
rank ring (line 3). That step rests on the Lean proof.

The addendum on finite von Neumann algebras (`VN.md`) is a paper proof. It is not formalized in Lean. Its Section 7
says who checked it.

## Licence

Apache License 2.0, see `LICENSE`.

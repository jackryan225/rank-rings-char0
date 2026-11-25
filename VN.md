# Addendum: finite von Neumann algebras

Added on 25 November 2026. **Paper proof. Not checked in Lean. Not refereed.**

The Lean theorems of this repository are about rank ultraproducts of matrix rings. This file adds a second family of
targets: the rings of operators affiliated with finite von Neumann algebras. The statements and the proof below are
not in Lean. Section 7 says who checked them.

## 1. Statements

### Definitions

- `M` is a finite von Neumann algebra. Until Section 5 it has a faithful normal tracial state `τ` (`τ(1) = 1`).
- `U = U(M)` is the ring of closed, densely defined operators affiliated with `M` (Murray and von Neumann). It
  contains `M` as a subring. It is a `*`-regular ring.
- Each `x` in `U` has a left support projection `s_l(x)` and a right support projection `s_r(x)` in `M`. The rank is
  `rk(x) = τ(s_l(x)) = τ(s_r(x))`. It is a rank function in the sense of `README.md`.
- Each principal right ideal of `U` is `eU` for exactly one projection `e` of `M`. Put `dim_τ(eU) = τ(e)`. For
  projections `e`, `e'` we have `eU ∩ e'U = (e ∧ e')U`.
- For an idempotent `f` of `U`, bounded or not, `r_f` is its range projection and `k_f` is its kernel projection.
  So `fU = r_f U` and `(1 - f)U = k_f U`.
- `(P, L)` is a finite projective plane of order `q` with `n = q² + q + 1` points. `σ : P → L` is a bijection. `E` is
  the set of pairs `(p, p')` of points with `p` on the line `σ(p')`. It has `(q + 1) n` elements.
- A *ring homomorphism* is additive and multiplicative. It is *unital* if it maps 1 to 1. It need not be injective,
  rank preserving, linear over a field, or compatible with an involution.

### Theorem A (the inequality)

For all idempotents `f_p` in `U(M)` (`p` in `P`):

    Σ_{(p,p') in E}  dim_τ( f_p U ∩ (1 - f_{p'}) U )   ≤   n (q + 1 + √q) / 4.

The left side is `Σ_E τ(r_{f_p} ∧ k_{f_{p'}})`. For `M = M_N(ℂ)` with the normalized trace this is line 1 of "The
mechanism in five lines" in `README.md` (Lean: `RankRings.ineq_C`). For commutative `M` it is an expander mixing bound
for the incidence graph of the plane.

### Theorem B (no homomorphism)

Let `q = 7`. Let `R` be a unital ring that contains a *configuration*: elements `f_p` (`p` in `P`) and, for each
`e = (p, p')` in `E`, elements `g_e`, `x_{e,i}`, `y_{e,i}` (`i = 0, 1, 2`) with

    f_p f_p = f_p,     f_p g_e = g_e,     f_{p'} g_e = 0,     y_{e,0} g_e x_{e,0} + y_{e,1} g_e x_{e,1} + y_{e,2} g_e x_{e,2} = 1.

Then `R` has no unital ring homomorphism into `U(M)`, for every nonzero finite von Neumann algebra `M`.

This is the Lean structure `RankRings.Config` (`RankRings/Main.lean`). The same statement holds for a ring that
contains elements with the relations of `B_7` as written in `README.md`. Section 5 gives the proof for both forms.

**The ring of this repository.** Lean proves `RankRings.main_core`: there is a countable regular ℚ-algebra `S` with a
rank function that contains a configuration. Lean proves that every ring with a configuration has no unital ring
homomorphism into a rank ultraproduct of matrix rings over fields of characteristic 0 (`RankRings.Gen.no_config`);
`elek_countable` is the result for this `S`. Theorem B applies to the same `S`.

### Corollary 1 (C*-algebras with a tracial state)

`S` has no unital ring homomorphism into a unital C*-algebra that has a tracial state. Examples of such targets:
`M_N(ℂ)`, every finite von Neumann algebra with a normal tracial state, every II₁ factor, the reduced C*-algebra of
every discrete group.

### Corollary 2 (maps that are not unital)

`S` has no nonzero ring homomorphism into `U(M)`, for every finite von Neumann algebra `M`.

### The combined statement

The countable regular rank ℚ-algebra `S` has no unital ring homomorphism into any rank ultraproduct of matrix rings
over fields of characteristic 0 (**Lean**), and none into `U(M)` for any nonzero finite von Neumann algebra `M`
(**paper proof, this file**).

Theorem A contains the matrix inequality of line 1. Theorem B does not contain the Lean theorem, and the Lean theorem
does not contain Theorem B: a rank ultraproduct of matrix rings is not a ring `U(M)`.

## 2. What is not claimed

- **Not checked in Lean.** Mathlib has no traces on von Neumann algebras and no affiliated operators at this time.
- **The open readings of Elek's question stay open.** `README.md` lists three: ℂ-algebras of countable dimension over
  ℂ, `*`-regular rings with maps that keep the involution, and targets over fields of positive characteristic. This
  addendum answers none of them. `S` is a ℚ-algebra without an involution, and `U(M)` has characteristic 0.
- **Nothing about groups.** For every group `G`, the group algebra `ℂ[G]` lies in `U(L(G))`, where Theorem A holds.
  So no ring of matrices over a group algebra contains a configuration. The result says nothing about sofic or
  hyperlinear groups, the Connes embedding problem, the Atiyah conjecture or the Kaplansky conjectures.
- **Finite AW*-algebras that are not von Neumann algebras** are not treated. The proof needs an additive trace.
- **Novelty** is a search result, not a proof. See Section 8.

## 3. Standard facts that the proof uses

For `U(M)`, its support projections and its rank: F. J. Murray, J. von Neumann, *On rings of operators*, Ann. of
Math. 37 (1936), 116-229; S. K. Berberian, *The regular ring of a finite AW\*-algebra*, Ann. of Math. 65 (1957),
224-240; W. Lück, *L²-Invariants: Theory and Applications to Geometry and K-Theory*, Springer, 2002, Chapter 8.

- (U1) `xU = s_l(x)U` for `x` in `U`. If `x = wx` for a projection `w`, then `s_l(x) ≤ w` and `rk(x) ≤ τ(w)`.
- (U2) `rk(x + y) ≤ rk(x) + rk(y)`, `rk(xy) ≤ rk(x)`, `rk(xy) ≤ rk(y)`, and so `|rk(x) - rk(y)| ≤ rk(x - y)`.
- (U3) For `a` in `U`, the spectral projections of `|a|` are in `M`, the operator `a·1_{[0,k]}(|a|)` is in `M` with
  norm at most `k`, and `τ(1_{(k,∞)}(|a|)) → 0` for `k → ∞`, because `τ` is normal.
- (U4) If `g` in `M` is invertible and `e` is a projection of `M`, let `e^g` be the projection onto `g(eH)`. Then
  `τ(e^g) = τ(e)`: in the polar decomposition `ge = v|ge|` we have `v*v = e` and `vv* = e^g`. Also
  `(e ∧ e')^g = e^g ∧ e'^g`, because `g` is a bijection of the Hilbert space.

Notation: `‖x‖₂² = τ(x*x)` and `⟨x, y⟩ = τ(y*x)` for `x`, `y` in `M`; `d = q + 1`.

## 4. Proof of Theorem A

### Step 1. Two projections from a bounded idempotent

Let `E` in `M` be an idempotent and `F = 1 - E`. Put `L(E) = E*E + F*F`. For each vector `ξ`,
`‖ξ‖² = ‖Eξ + Fξ‖² ≤ 2(‖Eξ‖² + ‖Fξ‖²)`, so `L(E) ≥ 1/2`. Write `L = L(E)` and put

    P = E L⁻¹,     Q = F L⁻¹.

From `FE = 0` we get `LE = E*E = E*L`, so `E L⁻¹ = L⁻¹ E*`. Then `P* = P`, `PE = E`, `EP = P` and `P² = P`. So `P` is
the range projection of `E`. In the same way `Q` is the range projection of `F`, which is the kernel projection of
`E`. Also

    P + Q = L⁻¹,     E L⁻¹ E* = P,     F L⁻¹ F* = Q,     τ(P) + τ(Q) = τ(E) + τ(F) = 1,

because `τ(P) = τ(EP) = τ(PE) = τ(E)`. (The matrix case is in Lean: `RankRings/Descent.lean`.)

### Step 2. The potential

Let `f_1, ..., f_n` be idempotents of `M`. For an invertible `g` in `M` put `E_i = g f_i g⁻¹`, let `P_i`, `Q_i` be the
projections of Step 1 for `E_i`, and put

    D(g) = Σ_i (P_i + Q_i - 1),     Φ(g) = Σ_i τ(log L(E_i)).

`D(g)` is self-adjoint, and `Φ(g) ≥ -n log 2` by Step 1. In the notation of (U4), `P_i = (r_{f_i})^g` and
`Q_i = (k_{f_i})^g`.

### Step 3. The first derivative

Fix `H = H*` in `M` and put `g_t = e^{tH} g`. Then `E_i(t) = e^{tH} E_i e^{-tH}` is differentiable in norm with
`E_i' = H E_i - E_i H`, and for `L_t = L(E_i(t))`:

    L' = 2(E*HE + F*HF) - HL - LH.

Claim: `d/dt τ(log L_t) = τ(L_t⁻¹ L_t')`. Proof. For a positive invertible `L`,
`log L = ∫₀^∞ ((1 + s)⁻¹ - (L + s)⁻¹) ds`. Put `R_t(s) = (L_t + s)⁻¹`. All `L_t` are at least `1/2`, and

    (R_t(s) - R_{t+h}(s)) / h = R_{t+h}(s) · ((L_{t+h} - L_t) / h) · R_t(s).

This converges in norm to `R_t(s) L_t' R_t(s)` for `h → 0`, and its norm is at most `K / (1/2 + s)²` with a constant
`K` for small `h`. This bound is integrable, so we can differentiate under the integral. Then move one resolvent
around the trace and use `∫₀^∞ (L + s)⁻² ds = L⁻¹`.

With the formula for `L'` and the identities of Step 1:

    d/dt τ(log L_t) = 2τ(H E L⁻¹ E*) + 2τ(H F L⁻¹ F*) - 2τ(H) = 2τ(H (P + Q - 1)),     so     dΦ/dt = 2 τ(H D(g_t)).

### Step 4. The second derivative

The range of `E_i(t)` is `e^{tH}` applied to the range of `E_i(0)`, and the same holds for the kernels. Let `V_t` be
the projection onto `e^{tH}(V_0 H)` for a projection `V_0`. It is differentiable in norm (for example
`P_i(t) = E_i(t) L_t⁻¹`). From `(1 - V_t) e^{tH} V_0 = 0` we get `V_t' x = (1 - V_t) H x` for `x` in the range of
`V_t`, so `V' V = (1 - V) H V`. With `V = V*` and `V² = V`:

    V' = (1 - V) H V + V H (1 - V),     τ(H V') = 2 ‖(1 - V) H V‖₂².

The terms `‖(1 - V) H V‖₂²` and `‖V H (1 - V)‖₂²` are equal, and both are parts of `τ(H²)`. So
`0 ≤ τ(H V') ≤ ‖H‖₂²`. There are `2n` projections `P_i`, `Q_i`. So

    0 ≤ d²Φ/dt² ≤ 4n ‖H‖₂².

### Step 5. Descent

Take `H = -D(g)`. By Steps 3 and 4 and Taylor's formula,
`Φ(e^{tH} g) ≤ Φ(g) - 2t ‖D(g)‖₂² + 2n t² ‖D(g)‖₂²`. At `t = 1/(2n)` this is `Φ(g) - ‖D(g)‖₂² / (2n)`. `Φ` is bounded
below. So

    inf_g ‖D(g)‖₂ = 0,

where `g` runs over the invertible elements of `M`. No minimizer is needed.

### Step 6. The incidence estimate

Number the points `1, ..., n`. Let `C_{ij} = 1` if `(i, j)` is in `E` and `C_{ij} = 0` if not. Each row sum and each
column sum of `C` is `d`, and `CᵀC = qI + J` with the all-ones matrix `J`, because two different lines meet in one
point. So `‖Cb‖² = q‖b‖²` for each family `b = (b_j)` of vectors of a Hilbert space with `Σ_j b_j = 0`.

Use the real Hilbert space of self-adjoint elements with the inner product `τ(xy)`. Put `A_i = 2P_i - 1` and
`B_j = 2Q_j - 1`. These have norm 1. Split off the means: `A_i = Ā + a_i` and `B_j = B̄ + b_j`. The cross terms vanish,
because the row sums and the column sums are constant. So

    Σ_{ij} C_{ij} ⟨A_i, B_j⟩  =  (d/n) ⟨Σ_i A_i, Σ_j B_j⟩ + Σ_{ij} C_{ij} ⟨a_i, b_j⟩
                              ≤  (d/(4n)) ‖Σ_i A_i + Σ_j B_j‖₂² + n√q
                              =  (d/n) ‖D(g)‖₂² + n√q.

By `τ(P_i) + τ(Q_i) = 1`, the left side is `4 Σ_E τ(P_i Q_j) - dn`. So

    4 Σ_E τ(P_i Q_j)  ≤  dn + n√q + (d/n) ‖D(g)‖₂²     for every invertible g in M.

### Step 7. Meets; bounded idempotents

For projections `P`, `Q` with meet `W`: `τ(PQ) - τ(W) = τ(P(Q - W)P) ≥ 0`. By (U4),
`τ(r_{f_i} ∧ k_{f_j}) = τ(P_i ∧ Q_j) ≤ τ(P_i Q_j)` for every `g`. With Steps 5 and 6:

    4 Σ_E τ(r_{f_i} ∧ k_{f_j})  ≤  dn + n√q  =  n (q + 1 + √q).

This is Theorem A for idempotents in `M`.

### Step 8. Unbounded idempotents

Let `e` in `U` be an idempotent and `p = r_e`. Then `pe = e`. Also `ep = p`: in the polar decomposition `e = v|e|`
put `c = φ(|e|) v*` with `φ(0) = 0` and `φ(t) = 1/t` for `t > 0`; then `ec = vv* = p`, so `ep = e·ec = ec = p`. So
`e = p + a` with `a = pe(1 - p)`. The operator `|a|` commutes with `p`, and `|a|p = 0`. Put
`a_k = a·1_{[0,k]}(|a|)`. By (U3), `a_k` is in `pM(1 - p)`. So `e_k = p + a_k` is an idempotent of `M` with
`e_k U = pU`, and `rk(e - e_k) ≤ τ(1_{(k,∞)}(|a|)) → 0`.

For an idempotent `h` of `U` and a projection `w`: `wU ∩ (1 - h)U = (w - s_r(hw))U`, so its dimension is
`τ(w) - rk(hw)`. If we replace `h` by `h_k`, this changes by at most `rk(h - h_k)`, by (U2).

Now replace each `f_i` by its truncation. The ideals `f_i U` do not change, and each term of the sum converges. Step 7
for the truncations gives Theorem A.

## 5. Proof of Theorem B

**With a faithful normal tracial state.** Suppose that a unital ring homomorphism maps a configuration into `U`. The
images satisfy the same relations. For `e = (p, p')` in `E` let `W = f_p U ∩ (1 - f_{p'}) U = wU` with a projection
`w`. From `f_p g_e = g_e` and `f_{p'} g_e = 0` we get `g_e = w g_e`, so `rk(g_e) ≤ dim_τ W` by (U1). Then

    1 = rk(1) = rk(Σ_i y_{e,i} g_e x_{e,i}) ≤ 3 rk(g_e) ≤ 3 dim_τ W.

(For the relations of `B_7` as in `README.md`, use `rk(x_{e,i}) ≤ dim_τ W` in the same way.) There are `8n` pairs in
`E`. With Theorem A for `q = 7`:

    8n / 3  ≤  Σ_E dim_τ W  ≤  n (8 + √7) / 4,     that is     8 ≤ 3√7,     that is     64 ≤ 63.

This is false.

**Every nonzero finite von Neumann algebra.** Let `M` be finite and nonzero, and let `T` be its centre-valued trace
(R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Volume II, Chapter 8). Take a normal
state `ρ` of the centre and let `z ≠ 0` be its support projection. Then `ρ∘T` is a faithful normal tracial state on
`zM`. The map `x ↦ zx` is a unital ring homomorphism from `U(M)` to `U(zM)`. So a unital ring homomorphism into `U(M)`
gives one into `U(zM)`, against the first part.

## 6. Proofs of the corollaries

**Corollary 1.** Let `A` be a unital C*-algebra with a tracial state `τ`, and let `(π, H, ξ)` be the GNS
representation of `τ`. Put `N = π(A)''` and `ω(x) = ⟨xξ, ξ⟩`. Then `ω` is a normal state on `N`. It is tracial on
`π(A)`, and so on `N` (Kaplansky density; pass to the strong limit in one factor at a time). It is faithful: if
`ω(x*x) = 0`, then `xξ = 0`, and `⟨x aξ, bξ⟩ = ω(b*xa) = ω(ab*x) = ⟨xξ, ba*ξ⟩ = 0` for `a`, `b` in `N`; the vectors
`aξ` are dense, so `x = 0`. So `N` is a nonzero finite von Neumann algebra, and `π` is a unital ring homomorphism
from `A` to `N`, a subring of `U(N)`. A unital ring homomorphism from `S` to `A` would give one from `S` to `U(N)`,
against Theorem B.

**Corollary 2.** Let `φ` be a nonzero ring homomorphism from `S` to `U(M)`. Then `e = φ(1)` is a nonzero idempotent,
and `φ` is a unital ring homomorphism into the ring `eUe`. As in Step 8, `e = p + a` with the range projection `p` of
`e` and `a = pe(1 - p)`. Then `a² = 0`, `ap = 0`, `pa = a`, and `(1 - a) p (1 + a) = e`. So `eUe` is isomorphic to
`pUp`. The ring `pUp` is `U(pMp)`: an operator `T` in `pUp` is `T_0 ⊕ 0` on `pH ⊕ (1 - p)H` with `T_0` affiliated with
`pMp`, and each operator affiliated with `pMp` gives such a `T`. The algebra `pMp` is nonzero and finite. So `S` has a
unital ring homomorphism into `U(pMp)`, against Theorem B.

## 7. Who checked this

- Three write-ups of the proof of Theorems A and B exist. One is by Claude (by Anthropic). Two are by GPT-6.2 Astra
  (by OpenAI); for the first of these, Astra got the bare statement without a proof. All three use the potential of
  Step 2, which is also the potential of the Lean proof for matrices. The proof in this file follows the second
  write-up by Astra, with the repairs from the readings.
- Line-by-line readings: Claude (several readers), and one hostile reading by GPT-6.2 Sol (by OpenAI). The hostile
  reading found no false step. It found gaps in the writing, among them the bound that permits the derivative under
  the integral in Step 3, the support identities behind (U1) to (U3), and the reduction to bounded idempotents. This
  file contains the repairs.
- Corollaries 1 and 2: written by Claude, checked by GPT-6.2 Sol. Its verdict for Corollary 2 was "correct after
  repairs" (the proof of `ep = p`, and the identity `pUp = U(pMp)`); the repairs are in this file.
- Gemini 4 Neon has not checked this addendum at the date above.
- No professional mathematician has refereed it. It is not checked in Lean.

The weakest step is Step 3 (the derivative of the trace of a logarithm along a path).

## 8. Earlier work

The change of inner product for matrices is due to F. Barthe (Invent. Math. 134 (1998)) and Z. Dvir, G. Hu
(arXiv:1412.0795); see `README.md`. We use only the approximate form: the infimum in Step 5 need not be attained.
For commutative `M`, Theorem A is an expander mixing bound.

On 25 November 2026 GPT-6.2 Sol ran a web search (168 queries; the places included arXiv, papers that cite Elek
1006.5378 and Dvir-Hu 1412.0795, MathOverflow and GitHub) for an earlier statement of Theorem A in `U(M)` or of a
regular rank ℚ-algebra with no unital ring homomorphism into any `U(M)`. It found none. Gaps of this search: the
citation indexes did not respond, and journals behind a paywall were not read. A search cannot prove that there is no
earlier source. If you know one, please open an issue.

import Mathlib

/-!
# Determinant inequalities (Lemma 1 and the descent step)

`ld X = log |det X|`. For positive definite `X`: `ld X ≤ tr X - n`. For positive definite `X, W`:
`ld X + ld W ≤ tr (X W) - n`. The descent step is an inequality for a Hermitian matrix of trace zero.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RankRings

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithm of the absolute value of the determinant. -/
noncomputable def ld (X : Matrix n n ℂ) : ℝ := Real.log ‖X.det‖

lemma ld_mul {X Y : Matrix n n ℂ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    ld (X * Y) = ld X + ld Y := by
  unfold ld
  rw [det_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hX) (norm_ne_zero_iff.2 hY)]

lemma ld_one : ld (1 : Matrix n n ℂ) = 0 := by simp [ld]

lemma ld_inv (X : Matrix n n ℂ) : ld X⁻¹ = - ld X := by
  unfold ld
  rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, Real.log_inv]

lemma ld_le_trace {X : Matrix n n ℂ} (hX : X.PosDef) :
    ld X ≤ X.trace.re - Fintype.card n := by
  have h1 : X.det = ∏ i, (hX.1.eigenvalues i : ℂ) := hX.1.det_eq_prod_eigenvalues
  have h2 : X.trace = ∑ i, (hX.1.eigenvalues i : ℂ) := hX.1.trace_eq_sum_eigenvalues
  have hpos := hX.eigenvalues_pos
  have h3 : ‖X.det‖ = ∏ i, hX.1.eigenvalues i := by
    rw [h1, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hpos i).le]
  have h4 : X.trace.re = ∑ i, hX.1.eigenvalues i := by
    rw [h2, Complex.re_sum]
    simp
  unfold ld
  rw [h3, h4, Real.log_prod (fun i _ => (hpos i).ne')]
  have : ∑ i, Real.log (hX.1.eigenvalues i) ≤ ∑ i, (hX.1.eigenvalues i - 1) :=
    Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hpos i)
  simpa [Finset.sum_sub_distrib] using this

lemma ld_add_ld_le {X W : Matrix n n ℂ} (hX : X.PosDef) (hW : W.PosDef) :
    ld X + ld W ≤ (X * W).trace.re - Fintype.card n := by
  obtain ⟨B, hB, rfl⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hW.isStrictlyPositive
  have hBdet : B.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hB).ne_zero
  have hXdet : X.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hX.isUnit).ne_zero
  have hBs : (star B).det ≠ 0 := by
    rw [star_eq_conjTranspose, det_conjTranspose]
    exact star_ne_zero.2 hBdet
  have hpd : (B * X * star B).PosDef := (IsUnit.posDef_star_right_conjugate_iff hB).2 hX
  have h := ld_le_trace hpd
  have e1 : ld (B * X * star B) = ld X + ld (star B * B) := by
    rw [ld_mul (by rw [det_mul]; exact mul_ne_zero hBdet hXdet) hBs, ld_mul hBdet hXdet,
      ld_mul hBs hBdet]
    ring
  have e2 : (B * X * star B).trace = (X * (star B * B)).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2] at h
  exact h

/-- The scalar inequality of the descent step. -/
lemma scalar_step {x : ℝ} (hx : |x| ≤ 1 / 4) :
    (1 - x) * (1 - x) * (4 * x + 1) - 1 - 2 * Real.log (1 - x) ≤ 4 * x - 2 * (x * x) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  have hpos : 0 < 1 - x := by linarith
  -- `-log (1-x) ≤ 1/(1-x) - 1 = x/(1-x) ≤ x + (4/3) x^2`
  have hlog : -Real.log (1 - x) ≤ x + 4 / 3 * (x * x) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h
    have h' : (1 - x)⁻¹ ≤ 1 + x + 4 / 3 * (x * x) := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg (mul_self_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 4 - x)]
    linarith
  nlinarith [mul_nonneg (mul_self_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 4 - x)]

/-- The descent step: a Hermitian `G` of trace zero with `-s ≤ G ≤ s`, and `T = 1 - G/(4s)`. -/
lemma step_ineq {G : Matrix n n ℂ} (hG : G.IsHermitian) {s : ℝ} (hs : 0 < s)
    (h1 : ((s : ℂ) • (1 : Matrix n n ℂ) - G).PosSemidef)
    (h2 : ((s : ℂ) • (1 : Matrix n n ℂ) + G).PosSemidef) (htr : G.trace = 0) :
    let T : Matrix n n ℂ := 1 - ((1 / (4 * s) : ℝ) : ℂ) • G
    T.IsHermitian ∧ T.det ≠ 0 ∧
      (T * T * (G + (s : ℂ) • 1)).trace.re - s * Fintype.card n - 2 * s * ld T
        ≤ -((G * G).trace.re / (8 * s)) := by
  intro T
  set U : Matrix n n ℂ := (hG.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set γ : n → ℝ := hG.eigenvalues with hγ
  have hGd : G = U * diagonal (fun i => (γ i : ℂ)) * star U := by
    conv_lhs => rw [hG.spectral_theorem]
    rfl
  have hGd' : star U * G * U = diagonal (fun i => (γ i : ℂ)) := by
    rw [hGd]
    calc star U * (U * diagonal (fun i => (γ i : ℂ)) * star U) * U
        = (star U * U) * diagonal (fun i => (γ i : ℂ)) * (star U * U) := by noncomm_ring
      _ = _ := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hlo : ∀ i, -s ≤ γ i := by
    have h := h2.conjTranspose_mul_mul_same U
    have e : Uᴴ * ((s : ℂ) • (1 : Matrix n n ℂ) + G) * U
        = diagonal (fun i => ((s + γ i : ℝ) : ℂ)) := by
      rw [← star_eq_conjTranspose, Matrix.mul_add, Matrix.add_mul, hGd', Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hUU]
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [e, posSemidef_diagonal_iff] at h
    intro i
    have := h i
    rw [Complex.zero_le_real] at this
    linarith
  have hhi : ∀ i, γ i ≤ s := by
    have h := h1.conjTranspose_mul_mul_same U
    have e : Uᴴ * ((s : ℂ) • (1 : Matrix n n ℂ) - G) * U
        = diagonal (fun i => ((s - γ i : ℝ) : ℂ)) := by
      rw [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, hGd', Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hUU]
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [e, posSemidef_diagonal_iff] at h
    intro i
    have := h i
    rw [Complex.zero_le_real] at this
    linarith
  set x : n → ℝ := fun i => γ i / (4 * s) with hx
  have hxb : ∀ i, |x i| ≤ 1 / 4 := by
    intro i
    rw [hx, abs_le]
    constructor
    · rw [le_div_iff₀ (by positivity)]; linarith [hlo i]
    · rw [div_le_iff₀ (by positivity)]; linarith [hhi i]
  have hγx : ∀ i, γ i = 4 * s * x i := by
    intro i
    simp only [hx]
    field_simp
  have hTd : T = U * diagonal (fun i => ((1 - x i : ℝ) : ℂ)) * star U := by
    have e : diagonal (fun i => ((1 - x i : ℝ) : ℂ))
        = (1 : Matrix n n ℂ) - ((1 / (4 * s) : ℝ) : ℂ) • diagonal (fun i => (γ i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hx]
        ring
      · simp [hij]
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU', Matrix.mul_smul, Matrix.smul_mul,
      ← hGd]
  have hUdet : U.det * (star U).det = 1 := by rw [← det_mul, hUU', det_one]
  have hTdet : T.det = ∏ i, ((1 - x i : ℝ) : ℂ) := by
    rw [hTd, det_mul, det_mul, det_diagonal]
    calc U.det * (∏ i, ((1 - x i : ℝ) : ℂ)) * (star U).det
        = (U.det * (star U).det) * ∏ i, ((1 - x i : ℝ) : ℂ) := by ring
      _ = _ := by rw [hUdet, one_mul]
  have hpos : ∀ i, 0 < 1 - x i := fun i => by
    have := (abs_le.1 (hxb i)).2
    linarith
  have hld : ld T = ∑ i, Real.log (1 - x i) := by
    unfold ld
    rw [hTdet, norm_prod, ← Real.log_prod (fun i _ => (hpos i).ne')]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hpos i).le]
  have conj_mul : ∀ A B : Matrix n n ℂ, (U * A * star U) * (U * B * star U)
      = U * (A * B) * star U := by
    intro A B
    calc (U * A * star U) * (U * B * star U) = U * A * (star U * U) * B * star U := by noncomm_ring
      _ = _ := by rw [hUU, Matrix.mul_one]; noncomm_ring
  have conj_tr : ∀ A : Matrix n n ℂ, (U * A * star U).trace = A.trace := by
    intro A
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hGs : G + (s : ℂ) • 1 = U * diagonal (fun i => ((γ i + s : ℝ) : ℂ)) * star U := by
    have e : diagonal (fun i => ((γ i + s : ℝ) : ℂ))
        = diagonal (fun i => (γ i : ℂ)) + (s : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU',
      ← hGd]
  have hA : (T * T * (G + (s : ℂ) • 1)).trace.re
      = ∑ i, (1 - x i) * (1 - x i) * (γ i + s) := by
    rw [hGs, hTd, conj_mul, conj_mul, conj_tr, diagonal_mul_diagonal, diagonal_mul_diagonal,
      trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hB : (G * G).trace.re = ∑ i, γ i * γ i := by
    rw [hGd, conj_mul, conj_tr, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hC : ∑ i, γ i = 0 := by
    have : G.trace = ∑ i, (γ i : ℂ) := hG.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h' := congrArg Complex.re this
    simpa using h'.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [IsHermitian]
    simp only [T]
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hG.eq]
    congr 2
    exact Complex.conj_ofReal _
  · rw [hTdet]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      exact_mod_cast (hpos i).ne'
  · rw [hA, hB, hld]
    have key : ∀ i, (1 - x i) * (1 - x i) * (γ i + s) - s - 2 * s * Real.log (1 - x i)
        ≤ γ i - γ i * γ i / (8 * s) := by
      intro i
      have h := mul_le_mul_of_nonneg_left (scalar_step (hxb i)) hs.le
      have e1 : (1 - x i) * (1 - x i) * (γ i + s) - s - 2 * s * Real.log (1 - x i)
          = s * ((1 - x i) * (1 - x i) * (4 * x i + 1) - 1 - 2 * Real.log (1 - x i)) := by
        rw [hγx i]; ring
      have e2 : γ i - γ i * γ i / (8 * s) = s * (4 * x i - 2 * (x i * x i)) := by
        rw [hγx i]
        field_simp
        ring
      rw [e1, e2]
      exact h
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_div, hC] at hsum
    linarith

end RankRings

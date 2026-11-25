import RankRings.LogDet

/-!
# The near-minimizer

For an idempotent matrix `E` put `L E = Eᴴ E + (1-E)ᴴ (1-E)` (positive definite). Then `P = E (L E)⁻¹` is the
orthogonal projection on the range of `E`, and `(1-E) (L E)⁻¹` the one on the kernel. The potential of a family
of idempotents is `∑ log det L (g fₚ g⁻¹) ≥ 0`. A near-minimizer is almost balanced.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RankRings

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Eᴴ E + (1-E)ᴴ (1-E)`. -/
def LL (E : Matrix n n ℂ) : Matrix n n ℂ := Eᴴ * E + (1 - E)ᴴ * (1 - E)

lemma LL_one_sub (E : Matrix n n ℂ) : LL (1 - E) = LL E := by
  unfold LL
  rw [sub_sub_cancel, add_comm]

lemma LL_posDef (E : Matrix n n ℂ) : (LL E).PosDef := by
  have h1 : (LL E).PosSemidef :=
    (posSemidef_conjTranspose_mul_self E).add (posSemidef_conjTranspose_mul_self (1 - E))
  refine PosDef.of_dotProduct_mulVec_pos h1.1 fun x hx => ?_
  have e : star x ⬝ᵥ (LL E *ᵥ x)
      = star (E *ᵥ x) ⬝ᵥ (E *ᵥ x) + star ((1 - E) *ᵥ x) ⬝ᵥ ((1 - E) *ᵥ x) := by
    unfold LL
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec (star x) Eᴴ, dotProduct_mulVec (star x) (1 - E)ᴴ, star_mulVec, star_mulVec]
  rw [e]
  by_cases h : E *ᵥ x = 0
  · have : (1 - E) *ᵥ x = x := by rw [sub_mulVec, one_mulVec, h, sub_zero]
    rw [h, this]
    simpa using dotProduct_star_self_pos_iff.2 hx
  · exact add_pos_of_pos_of_nonneg (dotProduct_star_self_pos_iff.2 h)
      (dotProduct_star_self_nonneg _)

lemma LL_inv_posDef (E : Matrix n n ℂ) : (LL E)⁻¹.PosDef := (LL_posDef E).inv

lemma LL_det_ne_zero (E : Matrix n n ℂ) : (LL E).det ≠ 0 :=
  ((isUnit_iff_isUnit_det _).1 (LL_posDef E).isUnit).ne_zero

lemma LL_mul_inv (E : Matrix n n ℂ) : LL E * (LL E)⁻¹ = 1 :=
  mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (LL_det_ne_zero E))

lemma LL_inv_mul (E : Matrix n n ℂ) : (LL E)⁻¹ * LL E = 1 :=
  nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (LL_det_ne_zero E))

/-- The orthogonal projection on the range of the idempotent `E`. -/
noncomputable def pr (E : Matrix n n ℂ) : Matrix n n ℂ := E * (LL E)⁻¹

section Idem

variable {E : Matrix n n ℂ} (hE : E * E = E)

include hE

lemma one_sub_idem : (1 - E) * (1 - E) = 1 - E := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, hE, sub_self, sub_zero]

lemma LL_mul : LL E * E = Eᴴ * E := by
  unfold LL
  rw [Matrix.add_mul, Matrix.mul_assoc, hE, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hE,
    sub_self, Matrix.mul_zero, add_zero]

lemma mul_LL : Eᴴ * LL E = Eᴴ * E := by
  have h := congrArg conjTranspose (LL_mul hE)
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, (LL_posDef E).1.eq] at h
  exact h

lemma pr_eq : pr E = (LL E)⁻¹ * Eᴴ := by
  unfold pr
  calc E * (LL E)⁻¹ = (LL E)⁻¹ * (LL E * E) * (LL E)⁻¹ := by
        rw [← Matrix.mul_assoc, LL_inv_mul, Matrix.one_mul]
    _ = (LL E)⁻¹ * (Eᴴ * LL E) * (LL E)⁻¹ := by rw [LL_mul hE, mul_LL hE]
    _ = (LL E)⁻¹ * Eᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, LL_mul_inv, Matrix.mul_one]

lemma pr_herm : (pr E)ᴴ = pr E := by
  conv_rhs => rw [pr_eq hE]
  unfold pr
  rw [conjTranspose_mul, (LL_inv_posDef E).1.eq]

lemma pr_mul : pr E * E = E := by
  rw [pr_eq hE, Matrix.mul_assoc, ← LL_mul hE, ← Matrix.mul_assoc, LL_inv_mul, Matrix.one_mul]

lemma mul_pr : E * pr E = pr E := by
  unfold pr
  rw [← Matrix.mul_assoc, hE]

lemma pr_idem : pr E * pr E = pr E := by
  nth_rewrite 2 [pr]
  rw [← Matrix.mul_assoc, pr_mul hE]
  rfl

lemma pr_posSemidef : (pr E).PosSemidef := by
  have : pr E = (pr E)ᴴ * pr E := by rw [pr_herm hE, pr_idem hE]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

lemma one_sub_pr_posSemidef : (1 - pr E).PosSemidef := by
  have : 1 - pr E = (1 - pr E)ᴴ * (1 - pr E) := by
    rw [conjTranspose_sub, conjTranspose_one, pr_herm hE, one_sub_idem (pr_idem hE)]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

lemma trace_pr : (pr E).trace = E.trace := by
  rw [← mul_pr hE, trace_mul_comm, pr_mul hE]

omit hE in
lemma pr_add_pr : pr E + pr (1 - E) = (LL E)⁻¹ := by
  unfold pr
  rw [LL_one_sub, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

lemma trace_LL_inv : (LL E)⁻¹.trace = Fintype.card n := by
  rw [← pr_add_pr, trace_add, trace_pr hE, trace_pr (one_sub_idem hE), trace_sub, trace_one]
  ring

lemma ld_LL_nonneg : 0 ≤ ld (LL E) := by
  have h := ld_le_trace (LL_inv_posDef E)
  rw [ld_inv, trace_LL_inv hE] at h
  simp at h
  exact h

/-- Comparison: `LL E` is the best positive definite matrix compatible with `E`. -/
lemma comparison {Z : Matrix n n ℂ} (hZ : Z.PosDef) (hEZ : E * Z = Z * Eᴴ) :
    ld (LL E) ≤ Z.trace.re - Fintype.card n - ld Z := by
  have h := ld_add_ld_le hZ (LL_posDef E)
  have e : (Z * LL E).trace = Z.trace := by
    have h1 : LL E = 1 - E - Eᴴ + (Eᴴ * E + Eᴴ * E) := by
      unfold LL
      rw [conjTranspose_sub, conjTranspose_one]
      noncomm_ring
    have a1 : (Z * Eᴴ).trace = (Z * E).trace := by rw [← hEZ, trace_mul_comm]
    have a2 : (Z * (Eᴴ * E)).trace = (Z * E).trace := by
      rw [← Matrix.mul_assoc, ← hEZ, trace_mul_comm, ← Matrix.mul_assoc, hE, trace_mul_comm]
    rw [h1, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add,
      trace_add, trace_add, trace_sub, trace_sub, a1, a2]
    ring
  rw [e] at h
  linarith

/-- The change of the potential under a Hermitian `T`. -/
lemma comparison_step {T T' : Matrix n n ℂ} (hT : T.IsHermitian) (hTT : T * T' = 1)
    (hTT' : T' * T = 1) :
    ld (LL (T * E * T')) ≤ ld (LL E) + (T * T * (LL E)⁻¹).trace.re - Fintype.card n - 2 * ld T := by
  have hTu : IsUnit T := IsUnit.of_mul_eq_one _ hTT
  have hTdet : T.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hTu).ne_zero
  have hE' : (T * E * T') * (T * E * T') = T * E * T' := by
    calc (T * E * T') * (T * E * T') = T * E * (T' * T) * E * T' := by noncomm_ring
      _ = T * (E * E) * T' := by rw [hTT', Matrix.mul_one]; noncomm_ring
      _ = _ := by rw [hE]
  have hZ : (T * (LL E)⁻¹ * T).PosDef := by
    have := (IsUnit.posDef_star_right_conjugate_iff (x := (LL E)⁻¹) hTu).2 (LL_inv_posDef E)
    rwa [star_eq_conjTranspose, hT.eq] at this
  have hT'h : T'ᴴ = T' := by
    have h1 : T'ᴴ * T = 1 := by
      have := congrArg conjTranspose hTT
      rwa [conjTranspose_mul, hT.eq, conjTranspose_one] at this
    calc T'ᴴ = T'ᴴ * (T * T') := by rw [hTT, Matrix.mul_one]
      _ = T' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hc : (T * E * T') * (T * (LL E)⁻¹ * T) = (T * (LL E)⁻¹ * T) * (T * E * T')ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, hT.eq, hT'h]
    calc (T * E * T') * (T * (LL E)⁻¹ * T) = T * E * (T' * T) * (LL E)⁻¹ * T := by noncomm_ring
      _ = T * (E * (LL E)⁻¹) * T := by rw [hTT', Matrix.mul_one]; noncomm_ring
      _ = T * ((LL E)⁻¹ * Eᴴ) * T := by
          have := pr_eq hE
          unfold pr at this
          rw [this]
      _ = T * (LL E)⁻¹ * (T * T') * Eᴴ * T := by rw [hTT, Matrix.mul_one]; noncomm_ring
      _ = _ := by noncomm_ring
  have h := comparison hE' hZ hc
  have e1 : (T * (LL E)⁻¹ * T).trace = (T * T * (LL E)⁻¹).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  have hLi : ((LL E)⁻¹).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).1 (LL_inv_posDef E).isUnit).ne_zero
  have e2 : ld (T * (LL E)⁻¹ * T) = 2 * ld T - ld (LL E) := by
    rw [ld_mul (by rw [det_mul]; exact mul_ne_zero hTdet hLi) hTdet, ld_mul hTdet hLi, ld_inv]
    ring
  rw [e1, e2] at h
  linarith

end Idem

/-- A near-minimizer of the potential is almost balanced. -/
theorem exists_balanced {P : Type*} [Fintype P] [Nonempty P] (f : P → Matrix n n ℂ)
    (hf : ∀ p, f p * f p = f p) {η : ℝ} (hη : 0 < η) :
    ∃ g g' : Matrix n n ℂ, g * g' = 1 ∧ g' * g = 1 ∧
      (∑ p, ((LL (g * f p * g'))⁻¹ - 1)).IsHermitian ∧
      ((∑ p, ((LL (g * f p * g'))⁻¹ - 1)) * (∑ p, ((LL (g * f p * g'))⁻¹ - 1))).trace.re ≤ η := by
  classical
  set s : ℝ := (Fintype.card P : ℝ) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    exact_mod_cast Fintype.card_pos
  have conj_idem : ∀ g g' : Matrix n n ℂ, g' * g = 1 → ∀ p,
      (g * f p * g') * (g * f p * g') = g * f p * g' := by
    intro g g' hg p
    calc (g * f p * g') * (g * f p * g') = g * f p * (g' * g) * f p * g' := by noncomm_ring
      _ = g * (f p * f p) * g' := by rw [hg, Matrix.mul_one]; noncomm_ring
      _ = _ := by rw [hf]
  let A : Set ℝ := {x | ∃ g g' : Matrix n n ℂ, g * g' = 1 ∧ g' * g = 1 ∧
    x = ∑ p, ld (LL (g * f p * g'))}
  have hAne : A.Nonempty := ⟨_, 1, 1, by simp, by simp, rfl⟩
  have hAbdd : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro x ⟨g, g', -, h2, rfl⟩
    exact Finset.sum_nonneg fun p _ => ld_LL_nonneg (conj_idem g g' h2 p)
  obtain ⟨x, ⟨g, g', h1, h2, rfl⟩, hlt⟩ :=
    Real.lt_sInf_add_pos hAne (show 0 < η / (8 * s) by positivity)
  refine ⟨g, g', h1, h2, ?_⟩
  set E : P → Matrix n n ℂ := fun p => g * f p * g' with hEdef
  have hE : ∀ p, E p * E p = E p := conj_idem g g' h2
  set G : Matrix n n ℂ := ∑ p, ((LL (E p))⁻¹ - 1) with hGdef
  have hGadd : G + (s : ℂ) • 1 = ∑ p, (LL (E p))⁻¹ := by
    rw [hGdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hsdef]
    simp [Nat.cast_smul_eq_nsmul]
  have hG : G.IsHermitian := by
    rw [IsHermitian, hGdef, conjTranspose_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [conjTranspose_sub, conjTranspose_one, (LL_inv_posDef _).1.eq]
  have hP2 : ((s : ℂ) • (1 : Matrix n n ℂ) + G).PosSemidef := by
    rw [add_comm, hGadd]
    exact posSemidef_sum _ fun p _ => (LL_inv_posDef _).posSemidef
  have hP1 : ((s : ℂ) • (1 : Matrix n n ℂ) - G).PosSemidef := by
    have e : (s : ℂ) • (1 : Matrix n n ℂ) - G
        = ∑ p, ((1 - pr (E p)) + (1 - pr (1 - E p))) := by
      have e1 : ∀ p, (1 - pr (E p)) + (1 - pr (1 - E p)) = 1 - ((LL (E p))⁻¹ - 1) := by
        intro p
        rw [← pr_add_pr (E := E p)]
        abel
      rw [Finset.sum_congr rfl fun p _ => e1 p, Finset.sum_sub_distrib, ← hGdef, Finset.sum_const,
        Finset.card_univ, hsdef]
      simp [Nat.cast_smul_eq_nsmul]
    rw [e]
    exact posSemidef_sum _ fun p _ =>
      (one_sub_pr_posSemidef (hE p)).add (one_sub_pr_posSemidef (one_sub_idem (hE p)))
  have htr : G.trace = 0 := by
    rw [hGdef, trace_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [trace_sub, trace_LL_inv (hE p), trace_one, sub_self]
  refine ⟨hG, ?_⟩
  obtain ⟨hTh, hTdet, hstep⟩ := step_ineq hG hs hP1 hP2 htr
  set T : Matrix n n ℂ := 1 - ((1 / (4 * s) : ℝ) : ℂ) • G with hTdef
  have hTT : T * T⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hTdet)
  have hTT' : T⁻¹ * T = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hTdet)
  have hmem : ∑ p, ld (LL ((T * g) * f p * (g' * T⁻¹))) ∈ A := by
    refine ⟨T * g, g' * T⁻¹, ?_, ?_, rfl⟩
    · calc T * g * (g' * T⁻¹) = T * (g * g') * T⁻¹ := by noncomm_ring
        _ = 1 := by rw [h1, Matrix.mul_one, hTT]
    · calc g' * T⁻¹ * (T * g) = g' * (T⁻¹ * T) * g := by noncomm_ring
        _ = 1 := by rw [hTT', Matrix.mul_one, h2]
  have hinf := csInf_le hAbdd hmem
  have hle : ∑ p, ld (LL ((T * g) * f p * (g' * T⁻¹)))
      ≤ ∑ p, (ld (LL (E p)) + (T * T * (LL (E p))⁻¹).trace.re - Fintype.card n - 2 * ld T) := by
    refine Finset.sum_le_sum fun p _ => ?_
    have e : (T * g) * f p * (g' * T⁻¹) = T * E p * T⁻¹ := by
      rw [hEdef]
      noncomm_ring
    rw [e]
    exact comparison_step (hE p) hTh hTT hTT'
  have hsum : ∑ p, (T * T * (LL (E p))⁻¹).trace.re = (T * T * (G + (s : ℂ) • 1)).trace.re := by
    rw [hGadd, Matrix.mul_sum, trace_sum, Complex.re_sum]
  have hfin : ∑ p, (ld (LL (E p)) + (T * T * (LL (E p))⁻¹).trace.re - Fintype.card n - 2 * ld T)
      = ∑ p, ld (LL (E p)) + (T * T * (G + (s : ℂ) • 1)).trace.re - s * Fintype.card n
        - 2 * s * ld T := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hsdef]
    ring
  rw [hfin] at hle
  have hfinal : (G * G).trace.re / (8 * s) ≤ η / (8 * s) := by linarith
  exact (div_le_div_iff_of_pos_right (by positivity)).1 hfinal

end RankRings

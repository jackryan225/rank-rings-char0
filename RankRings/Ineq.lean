module

public import RankRings.Descent
public import RankRings.Plane

@[expose] public section
/-!
# Theorem 1: the inequality for complex idempotents indexed by a projective plane
-/

open Matrix Configuration Configuration.ProjectivePlane
open scoped ComplexOrder

namespace RankRings

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrices as vectors of a Hilbert space (Frobenius inner product). -/
noncomputable def mvec (A : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma mvec_add (A B : Matrix n n ℂ) : mvec (A + B) = mvec A + mvec B := by
  unfold mvec; rfl

lemma mvec_zero : mvec (0 : Matrix n n ℂ) = 0 := by
  unfold mvec; rfl

lemma mvec_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ) :
    mvec (∑ i ∈ s, A i) = ∑ i ∈ s, mvec (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvec_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mvec_add, ih]

lemma inner_mvec (A B : Matrix n n ℂ) : inner ℂ (mvec A) (mvec B) = (Aᴴ * B).trace := by
  unfold mvec
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, trace, mul_apply, Fintype.sum_prod_type, diag, conjTranspose_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- The plane inequality for a complex Hilbert space, with the real part of the inner product. -/
lemma plane_ineq_C {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : P → H) (b : L → H) (M : ℝ) (ha : ∀ p, (inner ℂ (a p) (a p)).re = M)
    (hb : ∀ l, (inner ℂ (b l) (b l)).re = M) :
    ∑ l, ∑ p, inc p l * (inner ℂ (a p) (b l)).re
      ≤ √(order P L) * Fintype.card P * M
        + (order P L + 1) / Fintype.card P
          * ((inner ℂ (∑ p, a p + ∑ l, b l) (∑ p, a p + ∑ l, b l)).re / 4) := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have h := plane_ineq (P := P) (L := L) (H := H) a b M ha hb
  have e : ‖∑ p, a p + ∑ l, b l‖ ^ 2
      = (inner ℂ (∑ p, a p + ∑ l, b l) (∑ p, a p + ∑ l, b l)).re := by
    rw [← real_inner_self_eq_norm_sq]; rfl
  rw [e] at h
  exact h

section Idem

variable {E R : Matrix n n ℂ}

/-- `tr (P Q) ≥ tr R` when `R ≤ P` and `R ≤ Q` are orthogonal projections. -/
lemma trace_mul_ge {P Q R : Matrix n n ℂ} (hP : Pᴴ = P) (hP2 : P * P = P) (hQ : Qᴴ = Q)
    (hQ2 : Q * Q = Q) (hR : Rᴴ = R) (hRR : R * R = R) (hPR : P * R = R) (hQR : Q * R = R) :
    R.trace.re ≤ (P * Q).trace.re := by
  have hRQ : R * Q = R := by
    have := congrArg conjTranspose hQR
    rwa [conjTranspose_mul, hQ, hR] at this
  have hX : (Q - R).PosSemidef := by
    have : Q - R = (Q - R)ᴴ * (Q - R) := by
      rw [conjTranspose_sub, hQ, hR, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQ2, hQR,
        hRQ, hRR]
      abel
    rw [this]; exact posSemidef_conjTranspose_mul_self _
  have hY := hX.conjTranspose_mul_mul_same P
  rw [hP] at hY
  have h1 := hY.trace_nonneg
  have e : (P * (Q - R) * P).trace = (P * Q).trace - R.trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hP2, Matrix.mul_sub, trace_sub, hPR]
  rw [e] at h1
  have h2 := (Complex.nonneg_iff.1 h1).1
  simp only [Complex.zero_re, Complex.sub_re] at h2
  linarith

end Idem

/-- **Theorem 1.** -/
theorem ineq_C {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (σ : P ≃ L) (f : P → Matrix n n ℂ) (hf : ∀ p, f p * f p = f p)
    (r : P → P → Matrix n n ℂ)
    (hr : ∀ p p', p ∈ σ p' → r p p' * r p p' = r p p' ∧ f p * r p p' = r p p' ∧
      f p' * r p p' = 0) :
    4 * ∑ p', ∑ p, inc p (σ p') * (r p p').trace.re
      ≤ ((order P L + 1) + √(order P L)) * Fintype.card P * Fintype.card n := by
  classical
  have hPne : Nonempty P := by
    obtain ⟨p, -⟩ := @ProjectivePlane.exists_config P L _ _
    exact ⟨p⟩
  set q : ℝ := (order P L : ℝ) with hq
  set N : ℝ := (Fintype.card n : ℝ) with hN
  set nP : ℝ := (Fintype.card P : ℝ) with hnP
  have hnPpos : 0 < nP := by rw [hnP]; exact_mod_cast Fintype.card_pos
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, g', h1, h2, hG, hGη⟩ :=
    exists_balanced f hf (η := ε * nP / (q + 1)) (by positivity)
  set E : P → Matrix n n ℂ := fun p => g * f p * g' with hEdef
  have hE : ∀ p, E p * E p = E p := by
    intro p
    calc (g * f p * g') * (g * f p * g') = g * f p * (g' * g) * f p * g' := by noncomm_ring
      _ = g * (f p * f p) * g' := by rw [h2, Matrix.mul_one]; noncomm_ring
      _ = _ := by rw [hf]
  set G : Matrix n n ℂ := ∑ p, ((LL (E p))⁻¹ - 1) with hGdef
  -- the vectors
  set A : P → Matrix n n ℂ := fun p => pr (E p) + pr (E p) - 1 with hA
  set B : P → Matrix n n ℂ := fun p => pr (1 - E p) + pr (1 - E p) - 1 with hB
  have selfadj : ∀ {X : Matrix n n ℂ}, X * X = X →
      (pr X + pr X - 1)ᴴ = pr X + pr X - 1 := by
    intro X hX
    rw [conjTranspose_sub, conjTranspose_add, conjTranspose_one, pr_herm hX]
  have sq1 : ∀ {X : Matrix n n ℂ}, X * X = X →
      ((pr X + pr X - 1)ᴴ * (pr X + pr X - 1)).trace.re = N := by
    intro X hX
    rw [selfadj hX]
    have : (pr X + pr X - 1) * (pr X + pr X - 1) = (1 : Matrix n n ℂ) := by
      have h := pr_idem hX
      have e : (pr X + pr X - 1) * (pr X + pr X - 1)
          = (pr X * pr X + pr X * pr X + pr X * pr X + pr X * pr X) - pr X - pr X - pr X - pr X
            + 1 := by noncomm_ring
      rw [e, h]
      abel
    rw [this, trace_one, hN]
    simp
  have hplane := plane_ineq_C (P := P) (L := L) (fun p => mvec (A p))
    (fun l => mvec (B (σ.symm l))) N
    (fun p => by rw [inner_mvec]; exact sq1 (hE p))
    (fun l => by rw [inner_mvec]; exact sq1 (one_sub_idem (hE _)))
  -- the error term
  have hsumAB : ∑ p, mvec (A p) + ∑ l, mvec (B (σ.symm l)) = mvec (2 • G) := by
    rw [← mvec_sum, Equiv.sum_comp σ.symm (fun p => mvec (B p)), ← mvec_sum, ← mvec_add]
    congr 1
    rw [hGdef, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← pr_add_pr (E := E p), two_nsmul]
    simp only [hA, hB]
    first
      | abel
      | noncomm_ring
  have herr : (inner ℂ (mvec (2 • G)) (mvec (2 • G))).re ≤ 4 * (ε * nP / (q + 1)) := by
    rw [inner_mvec, two_nsmul, conjTranspose_add, hG.eq]
    simp only [Matrix.add_mul, Matrix.mul_add, trace_add, Complex.add_re]
    linarith
  rw [hsumAB] at hplane
  -- the main term
  have hterm : ∀ p p', (inner ℂ (mvec (A p)) (mvec (B p'))).re
      = 4 * (pr (E p) * pr (1 - E p')).trace.re - 2 * (f p).trace.re
        - 2 * (1 - f p').trace.re + N := by
    intro p p'
    rw [inner_mvec, selfadj (hE p)]
    have e1 : (pr (E p)).trace = (f p).trace := by
      rw [trace_pr (hE p), hEdef]
      simp only
      rw [trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    have e2 : (pr (1 - E p')).trace = (1 - f p').trace := by
      rw [trace_pr (one_sub_idem (hE p')), hEdef]
      simp only
      rw [trace_sub, trace_sub, trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    have e3 : (pr (E p) + pr (E p) - 1) * (pr (1 - E p') + pr (1 - E p') - 1)
        = (pr (E p) * pr (1 - E p') + pr (E p) * pr (1 - E p') + pr (E p) * pr (1 - E p')
          + pr (E p) * pr (1 - E p')) - pr (E p) - pr (E p) - pr (1 - E p') - pr (1 - E p') + 1 := by
      noncomm_ring
    rw [e3]
    simp only [trace_add, trace_sub, trace_one, e1, e2, Complex.sub_re, Complex.add_re, hN]
    simp only [Complex.natCast_re]
    ring
  have hlow : ∀ p p', p ∈ σ p' → (r p p').trace.re ≤ (pr (E p) * pr (1 - E p')).trace.re := by
    intro p p' hpp
    obtain ⟨hr1, hr2, hr3⟩ := hr p p' hpp
    set X : Matrix n n ℂ := g * r p p' * g' with hX
    have hX2 : X * X = X := by
      calc (g * r p p' * g') * (g * r p p' * g') = g * r p p' * (g' * g) * r p p' * g' := by
            noncomm_ring
        _ = g * (r p p' * r p p') * g' := by rw [h2, Matrix.mul_one]; noncomm_ring
        _ = _ := by rw [hr1]
    have hEX : E p * X = X := by
      calc (g * f p * g') * (g * r p p' * g') = g * f p * (g' * g) * r p p' * g' := by noncomm_ring
        _ = g * (f p * r p p') * g' := by rw [h2, Matrix.mul_one]; noncomm_ring
        _ = X := by rw [hr2]
    have hEX' : (1 - E p') * X = X := by
      have : E p' * X = 0 := by
        calc (g * f p' * g') * (g * r p p' * g') = g * f p' * (g' * g) * r p p' * g' := by
              noncomm_ring
          _ = g * (f p' * r p p') * g' := by rw [h2, Matrix.mul_one]; noncomm_ring
          _ = 0 := by rw [hr3]; simp
      rw [Matrix.sub_mul, this, Matrix.one_mul, sub_zero]
    have hPX : ∀ {Y : Matrix n n ℂ}, Y * Y = Y → Y * X = X → pr Y * pr X = pr X := by
      intro Y hY hYX
      have : pr Y * X = X := by rw [← hYX, ← Matrix.mul_assoc, pr_mul hY]
      show pr Y * (X * (LL X)⁻¹) = X * (LL X)⁻¹
      rw [← Matrix.mul_assoc, this]
    have htr : (pr X).trace.re = (r p p').trace.re := by
      rw [trace_pr hX2, hX, trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [← htr]
    exact trace_mul_ge (pr_herm (hE p)) (pr_idem (hE p)) (pr_herm (one_sub_idem (hE p')))
      (pr_idem (one_sub_idem (hE p'))) (pr_herm hX2) (pr_idem hX2) (hPX (hE p) hEX)
      (hPX (one_sub_idem (hE p')) hEX')
  -- assemble
  have hsum1 : ∑ l, ∑ p, inc p l * (inner ℂ (mvec (A p)) (mvec (B (σ.symm l)))).re
      = ∑ p', ∑ p, inc p (σ p') * (inner ℂ (mvec (A p)) (mvec (B p'))).re := by
    rw [← Equiv.sum_comp σ]
    simp
  rw [hsum1] at hplane
  have hsum2 : ∑ p', ∑ p, inc p (σ p') * (inner ℂ (mvec (A p)) (mvec (B p'))).re
      = 4 * ∑ p', ∑ p, inc p (σ p') * (pr (E p) * pr (1 - E p')).trace.re
        - (q + 1) * nP * N := by
    simp only [hterm, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have c1 : ∑ p', ∑ p, inc p (σ p') * (2 * (f p).trace.re) = 2 * (q + 1) * ∑ p, (f p).trace.re := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Equiv.sum_comp σ (fun l => inc p l), sum_inc_line]
      ring
    have c2 : ∑ p', ∑ p, inc p (σ p') * (2 * (1 - f p').trace.re)
        = 2 * (q + 1) * ∑ p', (1 - f p').trace.re := by
      simp only [← Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [sum_inc_point]
      ring
    have c3 : ∑ p', ∑ p, inc p (σ p') * N = (q + 1) * nP * N := by
      simp only [← Finset.sum_mul, sum_inc_point, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hnP]; ring
    have c4 : ∑ p', ∑ p, inc p (σ p') * (4 * (pr (E p) * pr (1 - E p')).trace.re)
        = 4 * ∑ p', ∑ p, inc p (σ p') * (pr (E p) * pr (1 - E p')).trace.re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    have c5 : ∑ p, (f p).trace.re + ∑ p, (1 - f p).trace.re = nP * N := by
      rw [← Finset.sum_add_distrib]
      simp only [trace_sub, trace_one, Complex.sub_re, add_sub_cancel, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, hN, hnP]
      simp
    rw [c1, c2, c3, c4]
    nlinarith [c5]
  rw [hsum2] at hplane
  have hmono : ∑ p', ∑ p, inc p (σ p') * (r p p').trace.re
      ≤ ∑ p', ∑ p, inc p (σ p') * (pr (E p) * pr (1 - E p')).trace.re := by
    refine Finset.sum_le_sum fun p' _ => Finset.sum_le_sum fun p _ => ?_
    unfold inc
    split_ifs with h
    · simpa using hlow p p' h
    · simp
  have hcoef : (q + 1) / nP * ((inner ℂ (mvec (2 • G)) (mvec (2 • G))).re / 4) ≤ ε := by
    have hq0 : 0 < q + 1 := by rw [hq]; positivity
    calc (q + 1) / nP * ((inner ℂ (mvec (2 • G)) (mvec (2 • G))).re / 4)
        ≤ (q + 1) / nP * ((4 * (ε * nP / (q + 1))) / 4) := by gcongr
      _ = ε := by field_simp
  have hsq : √q * nP * N = √q * nP * N := rfl
  nlinarith [hcoef, hmono, hplane]

end RankRings

end

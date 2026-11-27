module

public import Mathlib

@[expose] public section
/-!
# The inequality of the projective plane (expander mixing with the second singular value `√q`)
-/

open Configuration Configuration.ProjectivePlane

namespace RankRings

variable {P L : Type*} [Membership P L]

open Classical in
/-- The incidence matrix. -/
noncomputable def inc (p : P) (l : L) : ℝ := if p ∈ l then 1 else 0

section counts

variable [ProjectivePlane P L] [Fintype P] [Fintype L]

lemma sum_inc_line (p : P) : ∑ l : L, inc p l = order P L + 1 := by
  classical
  have h := lineCount_eq (L := L) p
  unfold lineCount at h
  have h2 : ∑ l : L, inc p l = ((Finset.univ.filter fun l : L => p ∈ l).card : ℝ) := by
    unfold inc
    rw [Finset.sum_boole]
  rw [h2]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact_mod_cast h

lemma sum_inc_point (l : L) : ∑ p : P, inc p l = order P L + 1 := by
  classical
  have h := pointCount_eq (P := P) l
  unfold pointCount at h
  have h2 : ∑ p : P, inc p l = ((Finset.univ.filter fun p : P => p ∈ l).card : ℝ) := by
    unfold inc
    rw [Finset.sum_boole]
  rw [h2]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact_mod_cast h

omit [Fintype P] in
open Classical in
lemma sum_inc_inc [Finite P] (p p' : P) :
    ∑ l : L, inc p l * inc p' l = 1 + (order P L : ℝ) * (if p = p' then 1 else 0) := by
  have := Fintype.ofFinite P
  by_cases h : p = p'
  · subst h
    have : ∀ l : L, inc p l * inc p l = inc p l := by
      intro l; unfold inc; split_ifs <;> simp
    simp only [this, sum_inc_line, ite_true]
    ring
  · have : ∀ l : L, inc p l * inc p' l
        = if l = (HasLines.mkLine h : L) then 1 else 0 := by
      intro l
      unfold inc
      have hm := HasLines.mkLine_ax (P := P) (L := L) h
      by_cases h1 : l = (HasLines.mkLine h : L)
      · subst h1; simp [hm.1, hm.2]
      · simp only [h1, ite_false]
        by_cases h2 : p ∈ l
        · have h3 : p' ∉ l := fun h3 =>
            h1 ((Nondegenerate.eq_or_eq h2 h3 hm.1 hm.2).resolve_left h)
          simp [h3]
        · simp [h2]
    simp [this, h]

end counts

variable [ProjectivePlane P L] [Fintype P] [Fintype L]

/-- The mixing inequality. -/
theorem plane_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : P → H) (b : L → H) (M : ℝ) (ha : ∀ p, inner ℝ (a p) (a p) = M)
    (hb : ∀ l, inner ℝ (b l) (b l) = M) :
    ∑ l, ∑ p, inc p l * inner ℝ (a p) (b l)
      ≤ √(order P L) * Fintype.card P * M
        + (order P L + 1) / Fintype.card P * (‖∑ p, a p + ∑ l, b l‖ ^ 2 / 4) := by
  classical
  set q : ℝ := (order P L : ℝ) with hq
  have hq1 : 1 < q := by
    have := one_lt_order P L
    rw [hq]; exact_mod_cast this
  set N : ℝ := (Fintype.card P : ℝ) with hN
  have hcard : N = q ^ 2 + q + 1 := by
    rw [hN, hq, card_points P L]; push_cast; ring
  have hcardL : (Fintype.card L : ℝ) = N := by
    rw [hcard, hq, card_lines P L]; push_cast; ring
  have hNpos : 0 < N := by rw [hcard]; positivity
  set A : H := ∑ p, a p with hA
  set B : H := ∑ l, b l with hB
  set s : L → H := fun l => ∑ p, inc p l • a p with hs
  set c : ℝ := (q + 1) / N with hc
  have hcN : c * N = q + 1 := by rw [hc]; field_simp
  -- second moment
  have h1 : ∑ l, inner ℝ (s l) (s l) = q * (N * M) + inner ℝ A A := by
    have e1 : ∀ l, inner ℝ (s l) (s l)
        = ∑ p, ∑ p', inc p l * inc p' l * inner ℝ (a p) (a p') := by
      intro l
      simp only [hs, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
      ring
    simp only [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ p, ∑ l : L, ∑ p', inc p l * inc p' l * inner ℝ (a p) (a p')
        = ∑ p', (1 + q * (if p = p' then 1 else 0)) * inner ℝ (a p) (a p') := by
      intro p
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [← Finset.sum_mul, sum_inc_inc]
    simp only [e2, add_mul, one_mul, Finset.sum_add_distrib]
    have e3 : ∑ p, ∑ p', inner ℝ (a p) (a p') = inner ℝ A A := by
      rw [hA, sum_inner]
      simp only [inner_sum]
    have e4 : ∑ p, ∑ p', q * (if p = p' then 1 else 0) * inner ℝ (a p) (a p') = q * (N * M) := by
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hN]; ring
    rw [e3, e4]; ring
  have h2 : ∑ l, s l = (q + 1) • A := by
    simp only [hs]
    rw [Finset.sum_comm, hA, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_smul, sum_inc_line]
  -- centered
  set C : L → H := fun l => s l - c • A with hC
  have h3 : ∑ l, inner ℝ (C l) (C l) ≤ q * (N * M) := by
    have e1 : ∀ l, inner ℝ (C l) (C l)
        = inner ℝ (s l) (s l) - 2 * c * inner ℝ (s l) A + c * c * inner ℝ A A := by
      intro l
      simp only [hC, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm A]
      rw [real_inner_comm (s l) A]
      ring
    have e2 : 0 ≤ inner ℝ A A := real_inner_self_nonneg
    have e3 : 1 - 2 * c * (q + 1) + N * (c * c) ≤ 0 := by
      have : N * (c * c) = c * (q + 1) := by rw [← hcN]; ring
      rw [this]
      have h4 : 1 ≤ c * (q + 1) := by
        rw [hc, div_mul_eq_mul_div, le_div_iff₀ hNpos, hcard]
        nlinarith
      linarith
    calc ∑ l, inner ℝ (C l) (C l)
        = ∑ l, inner ℝ (s l) (s l) - 2 * c * ∑ l, inner ℝ (s l) A + ∑ _l : L, c * c * inner ℝ A A := by
          rw [Finset.sum_congr rfl fun l _ => e1 l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
      _ = q * (N * M) + inner ℝ A A - 2 * c * ((q + 1) * inner ℝ A A) + N * (c * c * inner ℝ A A) := by
          rw [h1, ← sum_inner, h2, real_inner_smul_left, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, hcardL]
      _ ≤ q * (N * M) := by nlinarith [mul_nonneg e2 (neg_nonneg.2 e3)]
  -- Cauchy-Schwarz
  have h4 : 2 * √q * ∑ l, inner ℝ (C l) (b l) ≤ 2 * q * (N * M) := by
    have hsq : √q * √q = q := Real.mul_self_sqrt (by linarith)
    have e1 : ∀ l, 2 * √q * inner ℝ (C l) (b l) ≤ inner ℝ (C l) (C l) + q * M := by
      intro l
      have := real_inner_self_nonneg (x := C l - √q • b l)
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hb]
        at this
      rw [real_inner_comm (C l) (b l)] at this
      have e : √q * (√q * M) = q * M := by rw [← mul_assoc, hsq]
      rw [e] at this
      linarith
    have e2 := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => e1 l
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcardL] at e2
    linarith
  have hsqpos : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have h5 : ∑ l, inner ℝ (C l) (b l) ≤ √q * N * M := by
    have hsq : √q * √q = q := Real.mul_self_sqrt (by linarith)
    have : 2 * √q * ∑ l, inner ℝ (C l) (b l) ≤ 2 * √q * (√q * N * M) := by
      calc _ ≤ 2 * q * (N * M) := h4
        _ = 2 * (√q * √q) * (N * M) := by rw [hsq]
        _ = _ := by ring
    exact le_of_mul_le_mul_left this (by positivity)
  have h6 : inner ℝ A B ≤ ‖A + B‖ ^ 2 / 4 := by
    have e1 := real_inner_self_nonneg (x := A - B)
    have e2 : ‖A + B‖ ^ 2 = inner ℝ (A + B) (A + B) := (real_inner_self_eq_norm_sq _).symm
    rw [e2]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right] at e1 ⊢
    rw [real_inner_comm A B] at *
    linarith
  have h7 : ∑ l, ∑ p, inc p l * inner ℝ (a p) (b l) = ∑ l, inner ℝ (C l) (b l) + c * inner ℝ A B := by
    have e1 : ∀ l, ∑ p, inc p l * inner ℝ (a p) (b l) = inner ℝ (C l) (b l) + c * inner ℝ A (b l) := by
      intro l
      simp only [hC, hs, inner_sub_left, sum_inner, real_inner_smul_left]
      ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum]
    rfl
  rw [h7]
  have hcpos : 0 ≤ c := by rw [hc]; positivity
  have := mul_le_mul_of_nonneg_left h6 hcpos
  linarith

end RankRings

end

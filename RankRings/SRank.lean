import Mathlib

/-!
# The rank at scale `r`

`srk r A` is the least rank of a matrix `A'` with all entries of `A - A'` of norm at most `r`.
Over an ultrametric field it is subadditive and `srk (r*s) (A*B) ≤ srk r A + srk s B`.
-/

open Matrix

namespace RankRings

variable {K : Type*} [NormedField K]
variable {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]

set_option linter.unusedSectionVars false

omit [Fintype m] in
lemma rank_add_le' {F : Type*} [Field F] (A B : Matrix m n F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank F (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank F ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

omit [Fintype m] in
lemma rank_neg_le {F : Type*} [Field F] (A : Matrix m n F) : (-A).rank ≤ A.rank := by
  classical
  have : -A = A * (-1 : Matrix n n F) := by simp
  rw [this]; exact rank_mul_le_left _ _

/-- The least rank of a matrix within entrywise distance `r`. -/
noncomputable def srk (r : ℝ) (A : Matrix m n K) : ℕ :=
  sInf {d | ∃ A' : Matrix m n K, A'.rank = d ∧ ∀ i j, ‖A i j - A' i j‖ ≤ r}

lemma srk_le {r : ℝ} {A A' : Matrix m n K} (h : ∀ i j, ‖A i j - A' i j‖ ≤ r) :
    srk r A ≤ A'.rank :=
  Nat.sInf_le ⟨A', rfl, h⟩

lemma exists_srk {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) :
    ∃ A' : Matrix m n K, A'.rank = srk r A ∧ ∀ i j, ‖A i j - A' i j‖ ≤ r :=
  Nat.sInf_mem (s := {d | ∃ A' : Matrix m n K, A'.rank = d ∧ ∀ i j, ‖A i j - A' i j‖ ≤ r})
    ⟨A.rank, A, rfl, by simp [hr]⟩

lemma srk_le_rank {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) : srk r A ≤ A.rank :=
  srk_le (by simp [hr])

lemma srk_le_card {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) : srk r A ≤ Fintype.card n :=
  (srk_le_rank hr A).trans (rank_le_card_width A)

lemma srk_le_card_height {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) : srk r A ≤ Fintype.card m :=
  (srk_le_rank hr A).trans (rank_le_card_height A)

lemma srk_eq_zero_of_norm_le {r : ℝ} {A : Matrix m n K} (h : ∀ i j, ‖A i j‖ ≤ r) : srk r A = 0 :=
  Nat.eq_zero_of_le_zero ((srk_le (A' := 0) (by simpa using h)).trans (by simp))

lemma srk_anti {r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) (A : Matrix m n K) : srk r' A ≤ srk r A := by
  obtain ⟨A', h1, h2⟩ := exists_srk hr A
  rw [← h1]
  exact srk_le fun i j => (h2 i j).trans h

lemma srk_neg {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) : srk r (-A) ≤ srk r A := by
  obtain ⟨B', h1, h2⟩ := exists_srk hr A
  rw [← h1]
  refine (srk_le (A' := -B') fun i j => ?_).trans (rank_neg_le B')
  have := h2 i j
  rwa [Matrix.neg_apply, Matrix.neg_apply, neg_sub_neg, ← norm_neg, neg_sub]

lemma norm_mul_apply_le [IsUltrametricDist K] {A : Matrix m n K} {B : Matrix n o K} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i : m) (j : o) :
    ‖(A * B) i j‖ ≤ a * b := by
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

variable [IsUltrametricDist K]

lemma srk_add_le {r : ℝ} (hr : 0 ≤ r) (A B : Matrix m n K) :
    srk r (A + B) ≤ srk r A + srk r B := by
  obtain ⟨A', h1, h2⟩ := exists_srk hr A
  obtain ⟨B', h3, h4⟩ := exists_srk hr B
  rw [← h1, ← h3]
  refine (srk_le (A' := A' + B') fun i j => ?_).trans (rank_add_le' A' B')
  have e : (A + B) i j - (A' + B') i j = (A i j - A' i j) + (B i j - B' i j) := by
    simp only [Matrix.add_apply]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2 i j) (h4 i j))

lemma srk_sub_le {r : ℝ} (hr : 0 ≤ r) (A B : Matrix m n K) :
    srk r (A - B) ≤ srk r A + srk r B := by
  rw [sub_eq_add_neg]
  exact (srk_add_le hr A (-B)).trans (by have := srk_neg hr B; omega)

lemma srk_mul_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A : Matrix m n K) (B : Matrix n o K) :
    srk (r * s) (A * B) ≤ srk r A + srk s B := by
  classical
  obtain ⟨A', h1, h2⟩ := exists_srk hr A
  obtain ⟨B', h3, h4⟩ := exists_srk hs B
  rw [← h1, ← h3]
  have e : A * B - (A' * B + (A - A') * B') = (A - A') * (B - B') := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  refine (srk_le (A' := A' * B + (A - A') * B') fun i j => ?_).trans ?_
  · rw [← Matrix.sub_apply, e]
    exact norm_mul_apply_le hr hs (fun i j => h2 i j) (fun i j => h4 i j) i j
  · exact (rank_add_le' _ _).trans (add_le_add (rank_mul_le_left _ _) (rank_mul_le_right _ _))

/-- Multiplication by matrices with entries of norm at most one. -/
lemma srk_mul_right_le {r : ℝ} (hr : 0 ≤ r) (A : Matrix m n K) {B : Matrix n o K}
    (hB : ∀ i j, ‖B i j‖ ≤ 1) : srk r (A * B) ≤ srk r A := by
  have h := srk_mul_le hr zero_le_one A B
  rw [mul_one, srk_eq_zero_of_norm_le hB, add_zero] at h
  exact h

lemma srk_mul_left_le {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n K} (B : Matrix n o K)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) : srk r (A * B) ≤ srk r B := by
  have h := srk_mul_le zero_le_one hr A B
  rw [one_mul, srk_eq_zero_of_norm_le hA, zero_add] at h
  exact h

end RankRings

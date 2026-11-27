module

public import RankRings.SRank

@[expose] public section
/-!
# Smith normal form over an ultrametric field, and the rank at scale `r` of a diagonal matrix
-/

open Matrix

namespace RankRings

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

set_option linter.unusedSectionVars false

section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- All entries have norm at most one. -/
def Bdd {a b : Type*} (X : Matrix a b K) : Prop := ∀ i j, ‖X i j‖ ≤ 1

/-- Invertible with both the matrix and its inverse bounded. -/
def Uni (U : Matrix n n K) : Prop := ∃ U' : Matrix n n K, U * U' = 1 ∧ U' * U = 1 ∧ Bdd U ∧ Bdd U'

lemma Bdd.mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] {X : Matrix a b K} {Y : Matrix b c K} (hX : Bdd X)
    (hY : Bdd Y) : Bdd (X * Y) := fun i j => by
  simpa using norm_mul_apply_le zero_le_one zero_le_one hX hY i j

lemma bdd_one : Bdd (1 : Matrix n n K) := fun i j => by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma bdd_zero {a b : Type*} : Bdd (0 : Matrix a b K) := fun i j => by simp

lemma uni_one : Uni (1 : Matrix n n K) := ⟨1, by simp, by simp, bdd_one, bdd_one⟩

lemma Uni.mul {U V : Matrix n n K} (hU : Uni U) (hV : Uni V) : Uni (U * V) := by
  obtain ⟨U', h1, h2, h3, h4⟩ := hU
  obtain ⟨V', h5, h6, h7, h8⟩ := hV
  refine ⟨V' * U', ?_, ?_, h3.mul h7, h8.mul h4⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, h5, Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U', h2, Matrix.one_mul, h6]

lemma Uni.inv {U : Matrix n n K} (hU : Uni U) : ∃ U', Uni U' ∧ U * U' = 1 ∧ U' * U = 1 := by
  obtain ⟨U', h1, h2, h3, h4⟩ := hU
  exact ⟨U', ⟨U, h2, h1, h4, h3⟩, h1, h2⟩

lemma Uni.bdd {U : Matrix n n K} (hU : Uni U) : Bdd U := hU.choose_spec.2.2.1

lemma bdd_perm (σ : m ≃ n) : Bdd (σ.toPEquiv.toMatrix : Matrix m n K) := fun i j => by
  rw [PEquiv.toMatrix_apply]
  split_ifs <;> simp

lemma uni_perm (σ : n ≃ n) : Uni (σ.toPEquiv.toMatrix : Matrix n n K) := by
  refine ⟨σ.symm.toPEquiv.toMatrix, ?_, ?_, bdd_perm σ, bdd_perm σ.symm⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- `A = U * diagonal d * W` with `U, W` unimodular. -/
def HasSmith (A : Matrix n n K) : Prop :=
  ∃ U W : Matrix n n K, ∃ d : n → K, Uni U ∧ Uni W ∧ A = U * diagonal d * W

lemma hasSmith_of_uni {A U W : Matrix n n K} (hU : Uni U) (hW : Uni W)
    (h : HasSmith (U * A * W)) : HasSmith A := by
  obtain ⟨U1, W1, d, h1, h2, h3⟩ := h
  obtain ⟨U', hU', hUU', hU'U⟩ := hU.inv
  obtain ⟨W', hW', hWW', hW'W⟩ := hW.inv
  refine ⟨U' * U1, W1 * W', d, hU'.mul h1, h2.mul hW', ?_⟩
  calc A = (U' * U) * A * (W * W') := by rw [hU'U, hWW', Matrix.one_mul, Matrix.mul_one]
    _ = U' * (U * A * W) * W' := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3]; simp only [Matrix.mul_assoc]

lemma hasSmith_submatrix_perm {A : Matrix n n K} (σ τ : n ≃ n)
    (h : HasSmith (A.submatrix σ τ)) : HasSmith A := by
  have e : A.submatrix σ τ = σ.toPEquiv.toMatrix * A * τ.symm.toPEquiv.toMatrix := by
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp
  rw [e] at h
  exact hasSmith_of_uni (uni_perm σ) (uni_perm τ.symm) h

lemma uni_submatrix {U : Matrix m m K} (hU : Uni U) (e : n ≃ m) : Uni (U.submatrix e e) := by
  obtain ⟨U', h1, h2, h3, h4⟩ := hU
  refine ⟨U'.submatrix e e, ?_, ?_, fun i j => h3 _ _, fun i j => h4 _ _⟩
  · rw [submatrix_mul_equiv, h1, submatrix_one_equiv]
  · rw [submatrix_mul_equiv, h2, submatrix_one_equiv]

lemma hasSmith_of_equiv {A : Matrix m m K} (e : n ≃ m) (h : HasSmith (A.submatrix e e)) :
    HasSmith A := by
  obtain ⟨U, W, d, h1, h2, h3⟩ := h
  refine ⟨U.submatrix e.symm e.symm, W.submatrix e.symm e.symm, d ∘ e.symm,
    uni_submatrix h1 e.symm, uni_submatrix h2 e.symm, ?_⟩
  have : A = (A.submatrix e e).submatrix e.symm e.symm := by simp
  rw [this, h3, ← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _,
    submatrix_diagonal_equiv]

end

/-- The block step. -/
lemma hasSmith_sum {α : Type*} [Fintype α] [DecidableEq α]
    (ih : ∀ A : Matrix α α K, HasSmith A) (A : Matrix (Unit ⊕ α) (Unit ⊕ α) K)
    (hmax : ∀ i j, ‖A i j‖ ≤ ‖A (Sum.inl ()) (Sum.inl ())‖)
    (hne : A (Sum.inl ()) (Sum.inl ()) ≠ 0) : HasSmith A := by
  set a := A (Sum.inl ()) (Sum.inl ()) with ha
  set A11 := A.toBlocks₁₁
  have hA11 : A11 = diagonal fun _ => a := by
    ext i j
    rcases i; rcases j
    simp [A11, toBlocks₁₁, ha]
  have hinv : A11 * diagonal (fun _ => a⁻¹) = 1 := by
    rw [hA11, diagonal_mul_diagonal]
    ext i j; rcases i; rcases j; simp [hne]
  have hinv' : diagonal (fun _ => a⁻¹) * A11 = 1 := by
    rw [hA11, diagonal_mul_diagonal]
    ext i j; rcases i; rcases j; simp [hne]
  let _ : Invertible A11 := ⟨diagonal fun _ => a⁻¹, hinv', hinv⟩
  have hinvOf : ⅟A11 = diagonal fun _ => a⁻¹ := rfl
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 hne
  have hX : Bdd (A.toBlocks₂₁ * ⅟A11) := by
    intro i j
    rcases j
    rw [hinvOf, mul_diagonal, norm_mul, norm_inv]
    calc ‖A.toBlocks₂₁ i ()‖ * ‖a‖⁻¹ ≤ ‖a‖ * ‖a‖⁻¹ := by
          gcongr; exact hmax _ _
      _ = 1 := mul_inv_cancel₀ hapos.ne'
  have hY : Bdd (⅟A11 * A.toBlocks₁₂) := by
    intro i j
    rcases i
    rw [hinvOf, diagonal_mul, norm_mul, norm_inv]
    calc ‖a‖⁻¹ * ‖A.toBlocks₁₂ () j‖ ≤ ‖a‖⁻¹ * ‖a‖ := by
          gcongr; exact hmax _ _
      _ = 1 := inv_mul_cancel₀ hapos.ne'
  have hlow : ∀ X : Matrix α Unit K, Bdd X → Uni (fromBlocks 1 0 X 1) := by
    intro X hX
    refine ⟨fromBlocks 1 0 (-X) 1, ?_, ?_, ?_, ?_⟩
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, hX _ _]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, hX _ _]
  have hup : ∀ X : Matrix Unit α K, Bdd X → Uni (fromBlocks 1 X 0 1) := by
    intro X hX
    refine ⟨fromBlocks 1 (-X) 0 1, ?_, ?_, ?_, ?_⟩
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, hX _ _]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, hX _ _]
  have hdiag : ∀ U : Matrix α α K, Uni U → Uni (fromBlocks (1 : Matrix Unit Unit K) 0 0 U) := by
    intro U hU
    obtain ⟨U', h1, h2, h3, h4⟩ := hU
    refine ⟨fromBlocks 1 0 0 U', ?_, ?_, ?_, ?_⟩
    · rw [fromBlocks_multiply]; simp [h1, fromBlocks_one]
    · rw [fromBlocks_multiply]; simp [h2, fromBlocks_one]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, h3 _ _, bdd_zero _ _]
    · rintro (i | i) (j | j) <;> simp [bdd_one _ _, h4 _ _, bdd_zero _ _]
  obtain ⟨U1, W1, d1, hU1, hW1, hD⟩ :=
    ih (A.toBlocks₂₂ - A.toBlocks₂₁ * ⅟A11 * A.toBlocks₁₂)
  have key := fromBlocks_eq_of_invertible₁₁ A11 A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
  rw [fromBlocks_toBlocks] at key
  refine ⟨fromBlocks 1 0 (A.toBlocks₂₁ * ⅟A11) 1 * fromBlocks 1 0 0 U1,
    fromBlocks 1 0 0 W1 * fromBlocks 1 (⅟A11 * A.toBlocks₁₂) 0 1,
    Sum.elim (fun _ => a) d1, (hlow _ hX).mul (hdiag _ hU1), (hdiag _ hW1).mul (hup _ hY), ?_⟩
  have hmid : fromBlocks A11 0 0 (A.toBlocks₂₂ - A.toBlocks₂₁ * ⅟A11 * A.toBlocks₁₂)
      = fromBlocks 1 0 0 U1 * diagonal (Sum.elim (fun _ => a) d1) * fromBlocks 1 0 0 W1 := by
    rw [hD, ← fromBlocks_diagonal, ← hA11, fromBlocks_multiply, fromBlocks_multiply]
    simp
  calc A = _ := key
    _ = fromBlocks 1 0 (A.toBlocks₂₁ * ⅟A11) 1 * (fromBlocks 1 0 0 U1 *
          diagonal (Sum.elim (fun _ => a) d1) * fromBlocks 1 0 0 W1) *
          fromBlocks 1 (⅟A11 * A.toBlocks₁₂) 0 1 := by rw [hmid]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem hasSmith_all : ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n K), HasSmith A := by
  intro n hn
  refine Fintype.induction_empty_option
    (P := fun n _ => ∀ [DecidableEq n] (A : Matrix n n K), HasSmith A) ?_ ?_ ?_ n
  · intro α β _ e h _ A
    classical
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact hasSmith_of_equiv e (h _)
  · intro _ A
    exact ⟨1, 1, 0, uni_one, uni_one, Subsingleton.elim _ _⟩
  · intro α _ ih _ A
    classical
    by_cases h0 : A = 0
    · exact ⟨1, 1, 0, uni_one, uni_one, by simp [h0]⟩
    · obtain ⟨⟨i0, j0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Option α × Option α))
        (fun ij => ‖A ij.1 ij.2‖) ⟨(none, none), Finset.mem_univ _⟩
      have hne : A i0 j0 ≠ 0 := by
        intro h
        apply h0
        ext i j
        have := hmax (i, j) (Finset.mem_univ _)
        simp only [h, norm_zero] at this
        simpa using norm_le_zero_iff.1 this
      apply hasSmith_submatrix_perm (Equiv.swap none i0) (Equiv.swap none j0)
      let e : Unit ⊕ α ≃ Option α :=
        { toFun := fun x => Sum.elim (fun _ => none) some x
          invFun := fun o => Option.elim o (Sum.inl ()) Sum.inr
          left_inv := by rintro (u | a) <;> rfl
          right_inv := by rintro (_ | a) <;> rfl }
      apply hasSmith_of_equiv e
      apply hasSmith_sum (fun B => ih B)
      · intro i j
        simp only [submatrix_apply]
        have h1 := hmax ((Equiv.swap none i0) (e i), (Equiv.swap none j0) (e j)) (Finset.mem_univ _)
        have h2 : e (Sum.inl ()) = none := rfl
        rw [h2, Equiv.swap_apply_left, Equiv.swap_apply_left]
        exact h1
      · simp only [submatrix_apply]
        have h2 : e (Sum.inl ()) = none := rfl
        rw [h2, Equiv.swap_apply_left, Equiv.swap_apply_left]
        exact hne


section srk
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma srk_uni_le {r : ℝ} (hr : 0 ≤ r) {U W : Matrix n n K} (hU : Bdd U) (hW : Bdd W)
    (A : Matrix n n K) : srk r (U * A * W) ≤ srk r A :=
  (srk_mul_right_le hr _ hW).trans (srk_mul_left_le hr _ hU)

lemma srk_uni {r : ℝ} (hr : 0 ≤ r) {U W : Matrix n n K} (hU : Uni U) (hW : Uni W)
    (A : Matrix n n K) : srk r (U * A * W) = srk r A := by
  refine le_antisymm (srk_uni_le hr hU.bdd hW.bdd A) ?_
  obtain ⟨U', hU', h1, h2⟩ := hU.inv
  obtain ⟨W', hW', h3, h4⟩ := hW.inv
  have e : A = U' * (U * A * W) * W' := by
    calc A = (U' * U) * A * (W * W') := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]
      _ = U' * (U * A * W) * W' := by simp only [Matrix.mul_assoc]
  conv_lhs => rw [e]
  exact srk_uni_le hr hU'.bdd hW'.bdd _

/-- The rank at scale `r` of a diagonal matrix. -/
lemma srk_diagonal {r : ℝ} (hr : 0 ≤ r) (d : n → K) :
    srk r (diagonal d) = (Finset.univ.filter fun i => r < ‖d i‖).card := by
  classical
  set I := Finset.univ.filter fun i => r < ‖d i‖ with hI
  apply le_antisymm
  · set d' : n → K := fun i => if r < ‖d i‖ then d i else 0 with hd'
    refine (srk_le (A' := diagonal d') fun i j => ?_).trans ?_
    · by_cases hij : i = j
      · subst hij
        simp only [diagonal_apply_eq, hd']
        split_ifs with h
        · simp [hr]
        · simpa using not_lt.1 h
      · simp [hij, hr]
    · rw [rank_diagonal]
      apply le_of_eq
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp only [hd', Finset.mem_filter, Finset.mem_univ, true_and, hI]
      split_ifs with h
      · simp only [h, iff_true]
        intro h0
        rw [h0, norm_zero] at h
        exact (not_lt.2 hr) h
      · simp [h]
  · obtain ⟨A', h1, h2⟩ := exists_srk hr (diagonal d)
    rw [← h1]
    -- the block of `A'` on `I × I` is invertible
    set M : Matrix I I K := A'.submatrix (↑) (↑) with hM
    have hdet : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      obtain ⟨i1, -⟩ := Function.ne_iff.1 hv
      obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
        ⟨i1, Finset.mem_univ _⟩
      have hvpos : 0 < ‖v i0‖ := by
        by_contra hneg
        apply hv
        ext i
        have := hi0 i (Finset.mem_univ _)
        have h0' : ‖v i0‖ = 0 := le_antisymm (not_lt.1 hneg) (norm_nonneg _)
        rw [h0'] at this
        simpa using norm_le_zero_iff.1 this
      have hdi : r < ‖d i0‖ := (Finset.mem_filter.1 i0.2).2
      -- `(diag d - A')|_I v = d v` at `i0`
      have e1 : d i0 * v i0 = ∑ j : I, ((diagonal d) (i0 : n) (j : n) - A' i0 j) * v j := by
        have h3 : (M *ᵥ v) i0 = 0 := by rw [hMv]; rfl
        simp only [mulVec, dotProduct, hM, submatrix_apply] at h3
        have h4 : ∑ j : I, (diagonal d) (i0 : n) j * v j = d i0 * v i0 := by
          rw [Finset.sum_eq_single i0]
          · simp
          · intro j _ hj
            have : (i0 : n) ≠ j := fun h => hj (Subtype.ext h).symm
            simp [this]
          · simp
        simp only [sub_mul, Finset.sum_sub_distrib, h3, sub_zero]
        exact h4.symm
      have e2 : ‖∑ j : I, ((diagonal d) (i0 : n) (j : n) - A' i0 j) * v j‖ ≤ r * ‖v i0‖ := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul (h2 _ _) (hi0 j (Finset.mem_univ _)) (norm_nonneg _) hr
      rw [← e1, norm_mul] at e2
      have := (mul_le_mul_iff_left₀ hvpos).1 e2
      linarith
    have hrank : M.rank = Fintype.card I := rank_of_isUnit M ((isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 hdet))
    rw [Fintype.card_coe] at hrank
    rw [← hrank]
    -- a submatrix has smaller rank
    set L : Matrix I n K := Matrix.of fun i j => if (i : n) = j then 1 else 0
    set R : Matrix n I K := Matrix.of fun i j => if i = (j : n) then 1 else 0
    have e : M = L * A' * R := by
      ext i j
      simp only [hM, submatrix_apply, mul_apply, L, R, Matrix.of_apply, ite_mul, one_mul, zero_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [e]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

end srk

section qinv
variable {n : Type} [Fintype n] [DecidableEq n]

lemma bdd_diag_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {U W X : Matrix n n K} (hU : Bdd U) (hW : Bdd W)
    (hX : ∀ i j, ‖X i j‖ ≤ b) (i j : n) : ‖(U * X * W) i j‖ ≤ b := by
  have h1 : ∀ i j, ‖(U * X) i j‖ ≤ 1 * b := norm_mul_apply_le zero_le_one hb hU hX
  have := norm_mul_apply_le (by positivity) zero_le_one h1 hW i j
  simpa using this

/-- Quasi-inverse at scale `r`. -/
theorem exists_qinv (A : Matrix n n K) {r : ℝ} (hr : 0 < r) :
    ∃ B : Matrix n n K, (∀ i j, ‖(A * B * A - A) i j‖ ≤ r) ∧
      ∀ ρ : ℝ, r ≤ ρ → srk ρ⁻¹ B + srk ρ A ≤ srk r A := by
  classical
  obtain ⟨U, W, d, hU, hW, hA⟩ := hasSmith_all n A
  obtain ⟨U', hU', hUU', hU'U⟩ := hU.inv
  obtain ⟨W', hW', hWW', hW'W⟩ := hW.inv
  set b : n → K := fun i => if r < ‖d i‖ then (d i)⁻¹ else 0 with hb
  refine ⟨W' * diagonal b * U', ?_, ?_⟩
  · have e : A * (W' * diagonal b * U') * A - A = U * diagonal (fun i => d i * b i * d i - d i) * W := by
      rw [hA]
      have : U * diagonal d * W * (W' * diagonal b * U') * (U * diagonal d * W)
          = U * (diagonal d * (W * W') * diagonal b * (U' * U) * diagonal d) * W := by
        simp only [Matrix.mul_assoc]
      rw [this, hWW', hU'U, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal,
        diagonal_mul_diagonal, show diagonal (fun i => d i * b i * d i - d i)
          = diagonal (fun i => d i * b i * d i) - diagonal d from (diagonal_sub _ _).symm,
        Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    refine bdd_diag_mul zero_le_one hr.le hU.bdd hW.bdd (fun i j => ?_)
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, hb]
      dsimp only
      split_ifs with h
      · have : d i ≠ 0 := by
          intro h0; rw [h0, norm_zero] at h; linarith
        rw [mul_inv_cancel₀ this, one_mul, sub_self, norm_zero]; exact hr.le
      · simpa using not_lt.1 h
    · simp [hij, hr.le]
  · intro ρ hρ
    have hρ0 : 0 < ρ := hr.trans_le hρ
    rw [srk_uni (inv_nonneg.2 hρ0.le) hW' hU', srk_diagonal (inv_nonneg.2 hρ0.le), hA,
      srk_uni hρ0.le hU hW, srk_uni hr.le hU hW, srk_diagonal hρ0.le, srk_diagonal hr.le]
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hb] at hi ⊢
      rcases hi with h | h
      · split_ifs at h with h'
        · exact h'
        · simp at h; linarith [inv_pos.2 hρ0]
      · linarith
    · rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb] at h1 h2
      split_ifs at h1 with h'
      · rw [norm_inv] at h1
        have hdpos : 0 < ‖d i‖ := by linarith
        rw [inv_lt_inv₀ hρ0 hdpos] at h1
        linarith
      · simp at h1; linarith [inv_pos.2 hρ0]

end qinv

section blocks
variable {n : Type} [Fintype n] [DecidableEq n]

lemma uni_fromBlocks {U V : Matrix n n K} (hU : Uni U) (hV : Uni V) :
    Uni (fromBlocks U 0 0 V) := by
  obtain ⟨U', h1, h2, h3, h4⟩ := hU
  obtain ⟨V', h5, h6, h7, h8⟩ := hV
  refine ⟨fromBlocks U' 0 0 V', ?_, ?_, ?_, ?_⟩
  · rw [fromBlocks_multiply]; simp [h1, h5, fromBlocks_one]
  · rw [fromBlocks_multiply]; simp [h2, h6, fromBlocks_one]
  · rintro (i | i) (j | j) <;> simp [h3 _ _, h7 _ _]
  · rintro (i | i) (j | j) <;> simp [h4 _ _, h8 _ _]

lemma srk_fromBlocks_diag {r : ℝ} (hr : 0 ≤ r) (A B : Matrix n n K) :
    srk r (fromBlocks A 0 0 B) = srk r A + srk r B := by
  classical
  obtain ⟨U1, W1, d1, hU1, hW1, hA⟩ := hasSmith_all n A
  obtain ⟨U2, W2, d2, hU2, hW2, hB⟩ := hasSmith_all n B
  have e : fromBlocks A 0 0 B = fromBlocks U1 0 0 U2 * diagonal (Sum.elim d1 d2) *
      fromBlocks W1 0 0 W2 := by
    rw [hA, hB, ← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
    simp
  rw [e, srk_uni hr (uni_fromBlocks hU1 hU2) (uni_fromBlocks hW1 hW2), srk_diagonal hr, hA, hB,
    srk_uni hr hU1 hW1, srk_uni hr hU2 hW2, srk_diagonal hr, srk_diagonal hr]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  rfl

end blocks

end RankRings

end

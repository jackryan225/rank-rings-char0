import RankRings.Smith

/-!
# The rank algebra `S`: tight sequences modulo null sequences

`K` an ultrametric normed field, `ι k` finite index types, `ω` an ultrafilter on `ℕ`.
`u r A k = srk r (A k) / |ι k|`. Tight: `∀ ε > 0, ∃ R > 0, ∀ᶠ k, u R A k ≤ ε`.
Null: `∀ ε > 0, ∀ r > 0, ∀ᶠ k, u r A k ≤ ε`.
-/

open Matrix Filter

namespace RankRings

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable (ι : ℕ → Type) [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] [∀ k, Nonempty (ι k)]
variable (ω : Ultrafilter ℕ)

set_option linter.unusedSectionVars false

/-- Sequences of matrices. -/
abbrev Seq (K : Type*) [NormedField K] := ∀ k, Matrix (ι k) (ι k) K

variable {ι}

/-- normalized rank at scale `r` -/
noncomputable def uu (r : ℝ) (A : Seq ι K) (k : ℕ) : ℝ := (srk r (A k) : ℝ) / Fintype.card (ι k)

lemma card_pos' (k : ℕ) : (0 : ℝ) < Fintype.card (ι k) := by exact_mod_cast Fintype.card_pos

lemma uu_nonneg (r : ℝ) (A : Seq ι K) (k : ℕ) : 0 ≤ uu r A k := by
  unfold uu; positivity

lemma uu_le_one {r : ℝ} (hr : 0 ≤ r) (A : Seq ι K) (k : ℕ) : uu r A k ≤ 1 := by
  unfold uu
  rw [div_le_one (card_pos' k)]
  exact_mod_cast srk_le_card hr _

lemma uu_add_le {r : ℝ} (hr : 0 ≤ r) (A B : Seq ι K) (k : ℕ) :
    uu r (A + B) k ≤ uu r A k + uu r B k := by
  unfold uu
  rw [← add_div]
  gcongr
  exact_mod_cast srk_add_le hr (A k) (B k)

lemma uu_sub_le {r : ℝ} (hr : 0 ≤ r) (A B : Seq ι K) (k : ℕ) :
    uu r (A - B) k ≤ uu r A k + uu r B k := by
  unfold uu
  rw [← add_div]
  gcongr
  exact_mod_cast srk_sub_le hr (A k) (B k)

lemma uu_neg {r : ℝ} (hr : 0 ≤ r) (A : Seq ι K) (k : ℕ) : uu r (-A) k ≤ uu r A k := by
  unfold uu
  gcongr
  exact_mod_cast srk_neg hr (A k)

lemma uu_mul_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A B : Seq ι K) (k : ℕ) :
    uu (r * s) (A * B) k ≤ uu r A k + uu s B k := by
  unfold uu
  rw [← add_div]
  gcongr
  exact_mod_cast srk_mul_le hr hs (A k) (B k)

lemma uu_anti {r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) (A : Seq ι K) (k : ℕ) : uu r' A k ≤ uu r A k := by
  unfold uu
  gcongr
  exact_mod_cast srk_anti h hr (A k)

/-- tight sequences -/
def IsTight (A : Seq ι K) : Prop := ∀ ε > 0, ∃ R > 0, ∀ᶠ k in (ω : Filter ℕ), uu R A k ≤ ε

/-- null sequences -/
def IsNull (A : Seq ι K) : Prop := ∀ ε > 0, ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ ε

variable {ω}

lemma isTight_of_bdd {A : Seq ι K} (h : ∀ k, Bdd (A k)) : IsTight ω A := by
  intro ε hε
  refine ⟨1, one_pos, Eventually.of_forall fun k => ?_⟩
  unfold uu
  rw [srk_eq_zero_of_norm_le (h k)]
  simp [hε.le]

lemma isTight_add {A B : Seq ι K} (hA : IsTight ω A) (hB : IsTight ω B) : IsTight ω (A + B) := by
  intro ε hε
  obtain ⟨R1, hR1, h1⟩ := hA (ε / 2) (by positivity)
  obtain ⟨R2, hR2, h2⟩ := hB (ε / 2) (by positivity)
  refine ⟨max R1 R2, lt_max_of_lt_left hR1, ?_⟩
  filter_upwards [h1, h2] with k hk1 hk2
  calc uu (max R1 R2) (A + B) k ≤ uu (max R1 R2) A k + uu (max R1 R2) B k :=
        uu_add_le (by positivity) A B k
    _ ≤ uu R1 A k + uu R2 B k :=
        add_le_add (uu_anti (le_max_left _ _) hR1.le A k) (uu_anti (le_max_right _ _) hR2.le B k)
    _ ≤ ε := by linarith

lemma isTight_neg {A : Seq ι K} (hA : IsTight ω A) : IsTight ω (-A) := by
  intro ε hε
  obtain ⟨R, hR, h⟩ := hA ε hε
  exact ⟨R, hR, h.mono fun k hk => (uu_neg hR.le A k).trans hk⟩

lemma isTight_mul {A B : Seq ι K} (hA : IsTight ω A) (hB : IsTight ω B) : IsTight ω (A * B) := by
  intro ε hε
  obtain ⟨R1, hR1, h1⟩ := hA (ε / 2) (by positivity)
  obtain ⟨R2, hR2, h2⟩ := hB (ε / 2) (by positivity)
  refine ⟨R1 * R2, by positivity, ?_⟩
  filter_upwards [h1, h2] with k hk1 hk2
  have := uu_mul_le hR1.le hR2.le A B k
  linarith

variable (K ι ω) in
/-- The subalgebra of tight sequences. -/
def tight : Subalgebra K (Seq ι K) where
  carrier := {A | IsTight ω A}
  mul_mem' := isTight_mul
  add_mem' := isTight_add
  algebraMap_mem' c := by
    intro ε hε
    refine ⟨max 1 ‖c‖, lt_max_of_lt_left one_pos, Eventually.of_forall fun k => ?_⟩
    have h : srk (max 1 ‖c‖) ((algebraMap K (Seq ι K) c) k) = 0 := by
      apply srk_eq_zero_of_norm_le
      intro i j
      have e : (algebraMap K (Seq ι K) c) k = c • (1 : Matrix (ι k) (ι k) K) := by
        rw [Algebra.algebraMap_eq_smul_one]; rfl
      rw [e]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    unfold uu
    rw [h]
    simp [hε.le]

lemma isNull_add {A B : Seq ι K} (hA : IsNull ω A) (hB : IsNull ω B) : IsNull ω (A + B) := by
  intro ε hε r hr
  filter_upwards [hA (ε / 2) (by positivity) r hr, hB (ε / 2) (by positivity) r hr] with k h1 h2
  have := uu_add_le hr.le A B k
  linarith

lemma isNull_neg {A : Seq ι K} (hA : IsNull ω A) : IsNull ω (-A) := by
  intro ε hε r hr
  exact (hA ε hε r hr).mono fun k hk => (uu_neg hr.le A k).trans hk

lemma isNull_zero : IsNull ω (0 : Seq ι K) := by
  intro ε hε r hr
  refine Eventually.of_forall fun k => ?_
  unfold uu
  rw [srk_eq_zero_of_norm_le (by intro i j; simp [hr.le])]
  simp [hε.le]

lemma isNull_mul_left {A B : Seq ι K} (hA : IsTight ω A) (hB : IsNull ω B) : IsNull ω (A * B) := by
  intro ε hε r hr
  obtain ⟨R, hR, h1⟩ := hA (ε / 2) (by positivity)
  filter_upwards [h1, hB (ε / 2) (by positivity) (r / R) (by positivity)] with k hk1 hk2
  have := uu_mul_le hR.le (by positivity : (0 : ℝ) ≤ r / R) A B k
  rw [mul_div_cancel₀ _ hR.ne'] at this
  linarith

lemma isNull_mul_right {A B : Seq ι K} (hA : IsNull ω A) (hB : IsTight ω B) : IsNull ω (A * B) := by
  intro ε hε r hr
  obtain ⟨R, hR, h1⟩ := hB (ε / 2) (by positivity)
  filter_upwards [h1, hA (ε / 2) (by positivity) (r / R) (by positivity)] with k hk1 hk2
  have := uu_mul_le (by positivity : (0 : ℝ) ≤ r / R) hR.le A B k
  rw [div_mul_cancel₀ _ hR.ne'] at this
  linarith

lemma IsNull.isTight {A : Seq ι K} (hA : IsNull ω A) : IsTight ω A :=
  fun ε hε => ⟨1, one_pos, hA ε hε 1 one_pos⟩

variable (K ι ω) in
/-- Equality modulo null sequences. -/
def nullCon : RingCon (tight K ι ω) where
  r A B := IsNull ω ((A : Seq ι K) - (B : Seq ι K))
  iseqv := {
    refl := fun A => by
      rw [sub_self]
      exact isNull_zero
    symm := fun {A B} h => by
      have := isNull_neg h
      rwa [neg_sub] at this
    trans := fun {A B C} h1 h2 => by
      have := isNull_add h1 h2
      rwa [sub_add_sub_cancel] at this }
  add' := fun {A B C D} h1 h2 => by
    have := isNull_add h1 h2
    simp only [Subalgebra.coe_add]
    convert this using 1
    abel
  mul' := fun {A B C D} h1 h2 => by
    simp only [Subalgebra.coe_mul]
    have e : (A : Seq ι K) * C - B * D = (A - B) * C + B * (C - D) := by noncomm_ring
    rw [e]
    exact isNull_add (isNull_mul_right h1 C.2) (isNull_mul_left B.2 h2)

variable (K ι ω) in
/-- **The rank algebra.** -/
abbrev RR := (nullCon K ι ω).Quotient

end RankRings

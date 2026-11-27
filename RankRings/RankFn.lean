module

public import RankRings.RankRing

@[expose] public section
/-!
# The rank function on `RR K ι ω`, and von Neumann regularity
-/

open Matrix Filter

namespace RankRings

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {ι : ℕ → Type} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] [∀ k, Nonempty (ι k)]
variable {ω : Ultrafilter ℕ}

set_option linter.unusedSectionVars false

variable (ω) in
/-- The rank of a sequence: `inf {c ≥ 0 | ∀ r > 0, ∀ᶠ k, u r A k ≤ c}`. -/
noncomputable def rkS (A : Seq ι K) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ c}

lemma rkS_bdd (A : Seq ι K) :
    BddBelow {c | 0 ≤ c ∧ ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ c} := ⟨0, fun _ h => h.1⟩

lemma rkS_mem_one (A : Seq ι K) :
    (1 : ℝ) ∈ {c | 0 ≤ c ∧ ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ c} :=
  ⟨zero_le_one, fun r hr => Eventually.of_forall fun k => uu_le_one hr.le A k⟩

lemma rkS_nonneg (A : Seq ι K) : 0 ≤ rkS ω A :=
  le_csInf ⟨1, rkS_mem_one A⟩ fun _ h => h.1

lemma rkS_le_one (A : Seq ι K) : rkS ω A ≤ 1 := csInf_le (rkS_bdd A) (rkS_mem_one A)

lemma rkS_le_of {A : Seq ι K} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ c) : rkS ω A ≤ c :=
  csInf_le (rkS_bdd A) ⟨hc, h⟩

lemma eventually_of_rkS_lt {A : Seq ι K} {c : ℝ} (h : rkS ω A < c) :
    ∀ r > 0, ∀ᶠ k in (ω : Filter ℕ), uu r A k ≤ c := by
  obtain ⟨c', ⟨-, hc'⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨1, rkS_mem_one A⟩ h
  exact fun r hr => (hc' r hr).mono fun k hk => hk.trans hlt.le

lemma exists_of_lt_rkS {A : Seq ι K} {c : ℝ} (h : c < rkS ω A) :
    ∃ r > 0, ∀ᶠ k in (ω : Filter ℕ), c < uu r A k := by
  by_cases hc : c < 0
  · exact ⟨1, one_pos, Eventually.of_forall fun k => hc.trans_le (uu_nonneg _ _ _)⟩
  · by_contra hne
    push_neg at hne
    have : rkS ω A ≤ c := by
      refine rkS_le_of (not_lt.1 hc) fun r hr => ?_
      exact hne r hr
    linarith

lemma rkS_add_le (A B : Seq ι K) : rkS ω (A + B) ≤ rkS ω A + rkS ω B := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine rkS_le_of (by linarith [rkS_nonneg (ω := ω) A, rkS_nonneg (ω := ω) B]) fun r hr => ?_
  filter_upwards [eventually_of_rkS_lt (show rkS ω A < rkS ω A + ε / 2 by linarith) r hr,
    eventually_of_rkS_lt (show rkS ω B < rkS ω B + ε / 2 by linarith) r hr] with k h1 h2
  have := uu_add_le hr.le A B k
  linarith

lemma rkS_neg (A : Seq ι K) : rkS ω (-A) ≤ rkS ω A := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine rkS_le_of (by linarith [rkS_nonneg (ω := ω) A]) fun r hr => ?_
  filter_upwards [eventually_of_rkS_lt (show rkS ω A < rkS ω A + ε by linarith) r hr] with k h1
  exact (uu_neg hr.le A k).trans h1

lemma rkS_eq_zero_iff {A : Seq ι K} : rkS ω A = 0 ↔ IsNull ω A := by
  constructor
  · intro h ε hε r hr
    exact eventually_of_rkS_lt (by rw [h]; exact hε) r hr
  · intro h
    refine le_antisymm ?_ (rkS_nonneg A)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact rkS_le_of hε.le fun r hr => h ε hε r hr

lemma rkS_congr {A B : Seq ι K} (h : IsNull ω (A - B)) : rkS ω A = rkS ω B := by
  have h1 : rkS ω (A - B) = 0 := rkS_eq_zero_iff.2 h
  have h2 : rkS ω (B - A) = 0 := rkS_eq_zero_iff.2 (by simpa using isNull_neg h)
  apply le_antisymm
  · have := rkS_add_le (ω := ω) B (A - B)
    rw [add_sub_cancel, h1] at this
    linarith
  · have := rkS_add_le (ω := ω) A (B - A)
    rw [add_sub_cancel, h2] at this
    linarith

lemma rkS_mul_le_left (A : Seq ι K) {B : Seq ι K} (hB : IsTight ω B) :
    rkS ω (A * B) ≤ rkS ω A := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨R, hR, h1⟩ := hB (ε / 2) (by positivity)
  refine rkS_le_of (by linarith [rkS_nonneg (ω := ω) A]) fun r hr => ?_
  filter_upwards [h1, eventually_of_rkS_lt (show rkS ω A < rkS ω A + ε / 2 by linarith)
    (r / R) (by positivity)] with k hk1 hk2
  have := uu_mul_le (by positivity : (0 : ℝ) ≤ r / R) hR.le A B k
  rw [div_mul_cancel₀ _ hR.ne'] at this
  linarith

lemma rkS_mul_le_right {A : Seq ι K} (hA : IsTight ω A) (B : Seq ι K) :
    rkS ω (A * B) ≤ rkS ω B := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨R, hR, h1⟩ := hA (ε / 2) (by positivity)
  refine rkS_le_of (by linarith [rkS_nonneg (ω := ω) B]) fun r hr => ?_
  filter_upwards [h1, eventually_of_rkS_lt (show rkS ω B < rkS ω B + ε / 2 by linarith)
    (r / R) (by positivity)] with k hk1 hk2
  have := uu_mul_le hR.le (by positivity : (0 : ℝ) ≤ r / R) A B k
  rw [mul_div_cancel₀ _ hR.ne'] at this
  linarith

lemma uu_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) : uu r (1 : Seq ι K) k = 1 := by
  unfold uu
  have : (1 : Seq ι K) k = diagonal fun _ => (1 : K) := by
    rw [Pi.one_apply, diagonal_one]
  rw [this, srk_diagonal hr0]
  simp only [norm_one, hr1, Finset.filter_true, Finset.card_univ]
  rw [div_self (card_pos' k).ne']

lemma rkS_one : rkS ω (1 : Seq ι K) = 1 := by
  refine le_antisymm (rkS_le_one _) ?_
  by_contra h
  push_neg at h
  have := eventually_of_rkS_lt (show rkS ω (1 : Seq ι K) < (rkS ω (1 : Seq ι K) + 1) / 2 by linarith)
    (1 / 2) (by norm_num)
  obtain ⟨k, hk⟩ := this.exists
  rw [uu_one (by norm_num) (by norm_num)] at hk
  linarith

/-! ### The rank function on the quotient -/

variable (K ι ω) in
/-- The rank function of `RR K ι ω`. -/
noncomputable def rk : RR K ι ω → ℝ :=
  fun x => Quotient.liftOn' x (fun A => rkS ω (A : Seq ι K)) fun A B h => rkS_congr h

lemma rk_coe (A : tight K ι ω) : rk K ι ω (A : RR K ι ω) = rkS ω (A : Seq ι K) := rfl

lemma exists_rep (x : RR K ι ω) : ∃ A : tight K ι ω, (A : RR K ι ω) = x :=
  Quotient.inductionOn' x fun A => ⟨A, rfl⟩

lemma coe_eq_coe {A B : tight K ι ω} :
    (A : RR K ι ω) = (B : RR K ι ω) ↔ IsNull ω ((A : Seq ι K) - (B : Seq ι K)) :=
  RingCon.eq _

lemma rk_nonneg (x : RR K ι ω) : 0 ≤ rk K ι ω x := by
  obtain ⟨A, rfl⟩ := exists_rep x
  exact rkS_nonneg _

lemma rk_le_one (x : RR K ι ω) : rk K ι ω x ≤ 1 := by
  obtain ⟨A, rfl⟩ := exists_rep x
  exact rkS_le_one _

lemma rk_one : rk K ι ω 1 = 1 := by
  rw [← RingCon.coe_one, rk_coe]
  exact rkS_one

lemma rk_eq_zero_iff (x : RR K ι ω) : rk K ι ω x = 0 ↔ x = 0 := by
  obtain ⟨A, rfl⟩ := exists_rep x
  rw [rk_coe, rkS_eq_zero_iff, ← RingCon.coe_zero, coe_eq_coe]
  simp

lemma rk_add_le (x y : RR K ι ω) : rk K ι ω (x + y) ≤ rk K ι ω x + rk K ι ω y := by
  obtain ⟨A, rfl⟩ := exists_rep x
  obtain ⟨B, rfl⟩ := exists_rep y
  rw [← RingCon.coe_add, rk_coe, rk_coe, rk_coe]
  exact rkS_add_le _ _

lemma rk_mul_le_left (x y : RR K ι ω) : rk K ι ω (x * y) ≤ rk K ι ω x := by
  obtain ⟨A, rfl⟩ := exists_rep x
  obtain ⟨B, rfl⟩ := exists_rep y
  rw [← RingCon.coe_mul, rk_coe, rk_coe]
  exact rkS_mul_le_left _ B.2

lemma rk_mul_le_right (x y : RR K ι ω) : rk K ι ω (x * y) ≤ rk K ι ω y := by
  obtain ⟨A, rfl⟩ := exists_rep x
  obtain ⟨B, rfl⟩ := exists_rep y
  rw [← RingCon.coe_mul, rk_coe, rk_coe]
  exact rkS_mul_le_right A.2 _

/-! ### Additivity on orthogonal idempotents -/

section blocks
variable {n : Type} [Fintype n] [DecidableEq n]

lemma bdd_fromRows_one_zero : Bdd (fromRows (1 : Matrix n n K) (0 : Matrix n n K)) := by
  rintro (i | i) j
  · rw [fromRows_apply_inl]; exact bdd_one i j
  · rw [fromRows_apply_inr]; simp

lemma bdd_fromRows_zero_one : Bdd (fromRows (0 : Matrix n n K) (1 : Matrix n n K)) := by
  rintro (i | i) j
  · rw [fromRows_apply_inl]; simp
  · rw [fromRows_apply_inr]; exact bdd_one i j

lemma bdd_fromCols_one_zero : Bdd (fromCols (1 : Matrix n n K) (0 : Matrix n n K)) := by
  rintro i (j | j)
  · rw [fromCols_apply_inl]; exact bdd_one i j
  · rw [fromCols_apply_inr]; simp

lemma bdd_fromCols_zero_one : Bdd (fromCols (0 : Matrix n n K) (1 : Matrix n n K)) := by
  rintro i (j | j)
  · rw [fromCols_apply_inl]; simp
  · rw [fromCols_apply_inr]; exact bdd_one i j

lemma srk_fromBlocks_le {r : ℝ} (hr : 0 ≤ r) (X Y Z W : Matrix n n K) :
    srk r (fromBlocks X Y Z W) ≤ srk r X + srk r Y + srk r Z + srk r W := by
  have e : fromBlocks X Y Z W
      = fromRows (1 : Matrix n n K) (0 : Matrix n n K) * X * fromCols (1 : Matrix n n K) 0
      + fromRows (1 : Matrix n n K) (0 : Matrix n n K) * Y * fromCols (0 : Matrix n n K) 1
      + fromRows (0 : Matrix n n K) (1 : Matrix n n K) * Z * fromCols (1 : Matrix n n K) 0
      + fromRows (0 : Matrix n n K) (1 : Matrix n n K) * W * fromCols (0 : Matrix n n K) 1 := by
    have hh : ∀ (A B C D : Matrix n n K) (X : Matrix n n K),
        fromRows A B * X * fromCols C D = fromBlocks (A * X * C) (A * X * D) (B * X * C) (B * X * D) := by
      intro A B C D X
      rw [fromRows_mul, fromRows_mul_fromCols]
    rw [hh, hh, hh, hh]
    simp only [fromBlocks_add, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add]
  have key : ∀ {P : Matrix (n ⊕ n) n K} {Q : Matrix n (n ⊕ n) K} (X : Matrix n n K), Bdd P → Bdd Q →
      srk r (P * X * Q) ≤ srk r X := fun X hP hQ =>
    (srk_mul_right_le hr _ hQ).trans (srk_mul_left_le hr _ hP)
  rw [e]
  refine (srk_add_le hr _ _).trans (add_le_add ((srk_add_le hr _ _).trans (add_le_add
    ((srk_add_le hr _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · exact key X bdd_fromRows_one_zero bdd_fromCols_one_zero
  · exact key Y bdd_fromRows_one_zero bdd_fromCols_zero_one
  · exact key Z bdd_fromRows_zero_one bdd_fromCols_one_zero
  · exact key W bdd_fromRows_zero_one bdd_fromCols_zero_one

lemma srk_orth {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (E F : Matrix n n K) :
    srk r E + srk r F ≤ 2 * (srk R E + srk R F) + srk (r / (R * R)) (E + F)
      + (srk r (E * (E + F) * E - E) + srk r (E * (E + F) * F) + srk r (F * (E + F) * E)
        + srk r (F * (E + F) * F - F)) := by
  have hs : 0 ≤ r / (R * R) := by positivity
  set Col : Matrix (n ⊕ n) (n ⊕ n) K := fromBlocks E 0 F 0
  set M : Matrix (n ⊕ n) (n ⊕ n) K := fromBlocks (E + F) 0 0 0
  set Row : Matrix (n ⊕ n) (n ⊕ n) K := fromBlocks E F 0 0
  have hCMR : Col * (M * Row) = fromBlocks (E * (E + F) * E) (E * (E + F) * F) (F * (E + F) * E)
      (F * (E + F) * F) := by
    simp only [Col, M, Row, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_assoc]
  have e : fromBlocks E 0 0 F = Col * (M * Row) - fromBlocks (E * (E + F) * E - E)
      (E * (E + F) * F) (F * (E + F) * E) (F * (E + F) * F - F) := by
    rw [hCMR]
    ext (i | i) (j | j) <;> simp
  have h1 : srk r (fromBlocks E 0 0 F) = srk r E + srk r F := srk_fromBlocks_diag hr.le E F
  have h2 := srk_sub_le hr.le (Col * (M * Row)) (fromBlocks (E * (E + F) * E - E)
      (E * (E + F) * F) (F * (E + F) * E) (F * (E + F) * F - F))
  have h3 : srk r (Col * (M * Row)) ≤ srk R Col + (srk (r / (R * R)) M + srk R Row) := by
    have := srk_mul_le hR.le (mul_nonneg hs hR.le) Col (M * Row)
    have e' : R * (r / (R * R) * R) = r := by field_simp
    rw [e'] at this
    exact this.trans (add_le_add_right (srk_mul_le hs hR.le M Row) _)
  have h4 : srk R Col ≤ srk R E + srk R F := by
    have := srk_fromBlocks_le hR.le E 0 F 0
    simp only [srk_eq_zero_of_norm_le (r := R) (A := (0 : Matrix n n K)) (by simp [hR.le]),
      add_zero] at this
    exact this
  have h5 : srk R Row ≤ srk R E + srk R F := by
    have := srk_fromBlocks_le hR.le E F 0 0
    simp only [srk_eq_zero_of_norm_le (r := R) (A := (0 : Matrix n n K)) (by simp [hR.le]),
      add_zero] at this
    exact this
  have h6 : srk (r / (R * R)) M ≤ srk (r / (R * R)) (E + F) := by
    have := srk_fromBlocks_le hs (E + F) 0 0 0
    simp only [srk_eq_zero_of_norm_le (r := r / (R * R)) (A := (0 : Matrix n n K))
      (by simp [hs]), add_zero] at this
    exact this
  have h7 := srk_fromBlocks_le hr.le (E * (E + F) * E - E) (E * (E + F) * F) (F * (E + F) * E)
    (F * (E + F) * F - F)
  rw [e] at h1
  omega

end blocks

lemma uu_orth {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (E F : Seq ι K) (k : ℕ) :
    uu r E k + uu r F k ≤ 2 * (uu R E k + uu R F k) + uu (r / (R * R)) (E + F) k
      + (uu r (E * (E + F) * E - E) k + uu r (E * (E + F) * F) k + uu r (F * (E + F) * E) k
        + uu r (F * (E + F) * F - F) k) := by
  have h := srk_orth hr hR (E k) (F k)
  have hc := card_pos' (ι := ι) k
  set c : ℝ := (Fintype.card (ι k) : ℝ)
  have h' : ((srk r (E k) : ℝ) + srk r (F k)) / c ≤
      (2 * ((srk R (E k) : ℝ) + srk R (F k)) + srk (r / (R * R)) (E k + F k)
      + ((srk r (E k * (E k + F k) * E k - E k) : ℝ) + srk r (E k * (E k + F k) * F k)
        + srk r (F k * (E k + F k) * E k) + srk r (F k * (E k + F k) * F k - F k))) / c :=
    div_le_div_of_nonneg_right (by exact_mod_cast h) hc.le
  unfold uu
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  convert h' using 1 <;> ring

lemma rkS_add_orth {E F : Seq ι K} (hE : IsTight ω E) (hF : IsTight ω F)
    (h1 : IsNull ω (E * (E + F) * E - E)) (h2 : IsNull ω (E * (E + F) * F))
    (h3 : IsNull ω (F * (E + F) * E)) (h4 : IsNull ω (F * (E + F) * F - F)) :
    rkS ω E + rkS ω F ≤ rkS ω (E + F) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 20 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨r1, hr1, H1⟩ := exists_of_lt_rkS (show rkS ω E - δ < rkS ω E by linarith)
  obtain ⟨r2, hr2, H2⟩ := exists_of_lt_rkS (show rkS ω F - δ < rkS ω F by linarith)
  set r := min r1 r2
  have hr : 0 < r := lt_min hr1 hr2
  obtain ⟨R1, hR1, T1⟩ := hE δ hδ0
  obtain ⟨R2, hR2, T2⟩ := hF δ hδ0
  set R := max R1 R2
  have hR : 0 < R := lt_max_of_lt_left hR1
  have H3 := eventually_of_rkS_lt (show rkS ω (E + F) < rkS ω (E + F) + δ by linarith)
    (r / (R * R)) (by positivity)
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := (H1.and (H2.and (T1.and (T2.and
    (H3.and ((h1 δ hδ0 r hr).and ((h2 δ hδ0 r hr).and ((h3 δ hδ0 r hr).and
    (h4 δ hδ0 r hr))))))))).exists
  have a1 := uu_anti (min_le_left r1 r2) hr.le E k
  have a2 := uu_anti (min_le_right r1 r2) hr.le F k
  have a3 := uu_anti (le_max_left R1 R2) hR1.le E k
  have a4 := uu_anti (le_max_right R1 R2) hR2.le F k
  have := uu_orth hr hR E F k
  linarith

lemma rk_add_orth {e f : RR K ι ω} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hfe : f * e = 0) : rk K ι ω (e + f) = rk K ι ω e + rk K ι ω f := by
  refine le_antisymm (rk_add_le e f) ?_
  obtain ⟨E, rfl⟩ := exists_rep e
  obtain ⟨F, rfl⟩ := exists_rep f
  have n1 : ((E * (E + F) * E : tight K ι ω) : RR K ι ω) = (E : RR K ι ω) := by
    rw [RingCon.coe_mul, RingCon.coe_mul, RingCon.coe_add, mul_add, he, hef, add_zero, he]
  have n2 : ((E * (E + F) * F : tight K ι ω) : RR K ι ω) = ((0 : tight K ι ω) : RR K ι ω) := by
    rw [RingCon.coe_mul, RingCon.coe_mul, RingCon.coe_add, mul_add, he, hef, add_zero, hef,
      RingCon.coe_zero]
  have n3 : ((F * (E + F) * E : tight K ι ω) : RR K ι ω) = ((0 : tight K ι ω) : RR K ι ω) := by
    rw [RingCon.coe_mul, RingCon.coe_mul, RingCon.coe_add, mul_add, hfe, hf, zero_add, hfe,
      RingCon.coe_zero]
  have n4 : ((F * (E + F) * F : tight K ι ω) : RR K ι ω) = (F : RR K ι ω) := by
    rw [RingCon.coe_mul, RingCon.coe_mul, RingCon.coe_add, mul_add, hfe, hf, zero_add, hf]
  rw [coe_eq_coe] at n1 n2 n3 n4
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_zero, sub_zero] at n1 n2 n3 n4
  rw [← RingCon.coe_add, rk_coe, rk_coe, rk_coe, Subalgebra.coe_add]
  exact rkS_add_orth E.2 F.2 n1 n2 n3 n4

/-! ### Von Neumann regularity -/

theorem rr_regular (hω : ∀ j : ℕ, ∀ᶠ k in (ω : Filter ℕ), j ≤ k) (x : RR K ι ω) :
    ∃ y, x * y * x = x := by
  classical
  obtain ⟨A, rfl⟩ := exists_rep x
  set ρ := rkS ω (A : Seq ι K) with hρ
  set P : ℕ → ℕ → Prop := fun k j => uu (1 / ((j : ℝ) + 1)) (A : Seq ι K) k ≤ ρ + 1 / ((j : ℝ) + 1)
  have hP : ∀ j, ∀ᶠ k in (ω : Filter ℕ), P k j := fun j =>
    eventually_of_rkS_lt (lt_add_of_pos_right _ (by positivity)) _ (by positivity)
  set J : ℕ → ℕ := fun k => Nat.findGreatest (P k) k
  have hJ : ∀ k, P k (J k) := by
    intro k
    refine Nat.findGreatest_spec (P := P k) (m := 0) (Nat.zero_le k) ?_
    show uu (1 / ((0 : ℕ) + 1 : ℝ)) (A : Seq ι K) k ≤ ρ + 1 / ((0 : ℕ) + 1 : ℝ)
    have := uu_le_one (r := 1 / ((0 : ℕ) + 1 : ℝ)) (by positivity) (A : Seq ι K) k
    have := rkS_nonneg (ω := ω) (A : Seq ι K)
    simp only [Nat.cast_zero, zero_add, div_one] at *
    linarith
  have hJ' : ∀ j, ∀ᶠ k in (ω : Filter ℕ), j ≤ J k := fun j =>
    ((hω j).and (hP j)).mono fun k hk => Nat.le_findGreatest hk.1 hk.2
  set rr : ℕ → ℝ := fun k => 1 / ((J k : ℝ) + 1)
  have rr_pos : ∀ k, 0 < rr k := fun k => by positivity
  have rr_small : ∀ c > 0, ∀ᶠ k in (ω : Filter ℕ), rr k ≤ c := by
    intro c hc
    obtain ⟨j0, hj0⟩ := exists_nat_one_div_lt hc
    filter_upwards [hJ' j0] with k hk
    have : (j0 : ℝ) ≤ J k := by exact_mod_cast hk
    calc rr k = 1 / ((J k : ℝ) + 1) := rfl
      _ ≤ 1 / ((j0 : ℝ) + 1) := by gcongr
      _ ≤ c := hj0.le
  choose B hB1 hB2 using fun k => exists_qinv ((A : Seq ι K) k) (rr_pos k)
  have hBt : IsTight ω (B : Seq ι K) := by
    intro ε hε
    obtain ⟨r0, hr0, H⟩ := exists_of_lt_rkS (show ρ - ε / 2 < ρ by linarith)
    refine ⟨r0⁻¹, inv_pos.2 hr0, ?_⟩
    filter_upwards [H, rr_small (min r0 (ε / 2)) (by positivity)] with k hk1 hk2
    have h1 := hB2 k r0 (hk2.trans (min_le_left _ _))
    have h2 : uu r0⁻¹ (B : Seq ι K) k + uu r0 (A : Seq ι K) k ≤ uu (rr k) (A : Seq ι K) k := by
      unfold uu
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (card_pos' k).le
      exact_mod_cast h1
    have h3 : uu (rr k) (A : Seq ι K) k ≤ ρ + rr k := hJ k
    have h4 := hk2.trans (min_le_right _ _)
    linarith
  have hnull : IsNull ω ((A : Seq ι K) * B * (A : Seq ι K) - (A : Seq ι K)) := by
    intro ε hε r hr
    filter_upwards [rr_small r hr] with k hk
    unfold uu
    rw [srk_eq_zero_of_norm_le (fun i j => by
      simpa [Pi.mul_apply, Pi.sub_apply] using (hB1 k i j).trans hk)]
    simp [hε.le]
  refine ⟨((⟨B, hBt⟩ : tight K ι ω) : RR K ι ω), ?_⟩
  rw [← RingCon.coe_mul, ← RingCon.coe_mul, coe_eq_coe]
  simpa only [Subalgebra.coe_mul] using hnull

end RankRings

end

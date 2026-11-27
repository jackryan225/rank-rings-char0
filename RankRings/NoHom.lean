module

public import RankRings.Ineq
public import RankRings.SRank

@[expose] public section
/-! The complex side: no unital ring homomorphism from the relations of
`B_l` to a rank ultraproduct of complex matrix rings. Mathlib only, no epsilons in the statement. -/

open Matrix Configuration Configuration.ProjectivePlane

namespace RankRings

section Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- every complex matrix has a quasi-inverse -/
lemma exists_qinv_C (A : Matrix n n ℂ) : ∃ B : Matrix n n ℂ, A * B * A = A := by
  set f := Matrix.toLin' A
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  obtain ⟨t, ht⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  refine ⟨LinearMap.toMatrix' (t ∘ₗ s), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  have e1 : f v = (LinearMap.range f).subtype (f.rangeRestrict v) := rfl
  have e2 : s (f v) = f.rangeRestrict v := by
    rw [e1]; exact LinearMap.congr_fun hs _
  have e3 : f (t (f.rangeRestrict v)) = f v := by
    have h0 : f.rangeRestrict (t (f.rangeRestrict v)) = f.rangeRestrict v :=
      LinearMap.congr_fun ht (f.rangeRestrict v)
    have h' : f (t (f.rangeRestrict v)) = (LinearMap.range f).subtype
        (f.rangeRestrict (t (f.rangeRestrict v))) := rfl
    rw [h', h0]; rfl
  simp only [LinearMap.comp_apply]
  rw [e2, e3]

noncomputable def qinv (A : Matrix n n ℂ) : Matrix n n ℂ := (exists_qinv_C A).choose

lemma qinv_spec (A : Matrix n n ℂ) : A * qinv A * A = A := (exists_qinv_C A).choose_spec

/-- the trace of an idempotent complex matrix is its rank -/
lemma trace_eq_rank_of_idem {A : Matrix n n ℂ} (h : A * A = A) : A.trace = (A.rank : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' A) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ n), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at h1
  rw [h1, Matrix.rank]
  rfl

lemma rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le' _ _) (by omega)

end Basic


section Null

variable {I : Type} (ω : Ultrafilter I) (d : I → ℕ)

/-- sequences of complex matrices of sizes `d i` -/
abbrev MP := ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ

/-- normalized rank tends to `0` along `ω` -/
def IsRNull (a : MP d) : Prop :=
  Filter.Tendsto (fun i => ((a i).rank : ℝ) / d i) (ω : Filter I) (nhds 0)

variable {ω d}

lemma isRNull_of_le {a : MP d} (b : MP d) (h : ∀ i, (a i).rank ≤ (b i).rank) (hb : IsRNull ω d b) :
    IsRNull ω d a := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun i => ?_) (fun i => ?_)
  · positivity
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (h i)) (by positivity)

lemma isRNull_of_le_add {a : MP d} (b c : MP d) (h : ∀ i, (a i).rank ≤ (b i).rank + (c i).rank)
    (hb : IsRNull ω d b) (hc : IsRNull ω d c) : IsRNull ω d a := by
  have hbc := hb.add hc
  rw [add_zero] at hbc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbc (fun i => ?_) (fun i => ?_)
  · positivity
  · simp only
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h i) (by positivity)

lemma isRNull_zero : IsRNull ω d 0 := by
  unfold IsRNull
  simp only [Pi.zero_apply, Matrix.rank_zero, Nat.cast_zero, zero_div]
  exact tendsto_const_nhds

lemma isRNull_add {a b : MP d} (ha : IsRNull ω d a) (hb : IsRNull ω d b) : IsRNull ω d (a + b) :=
  isRNull_of_le_add a b (fun i => rank_add_le' _ _) ha hb

lemma isRNull_neg {a : MP d} (ha : IsRNull ω d a) : IsRNull ω d (-a) :=
  isRNull_of_le a (fun i => rank_neg_le _) ha

lemma isRNull_sub {a b : MP d} (ha : IsRNull ω d a) (hb : IsRNull ω d b) : IsRNull ω d (a - b) := by
  rw [sub_eq_add_neg]; exact isRNull_add ha (isRNull_neg hb)

lemma isRNull_mul_left (c : MP d) {a : MP d} (ha : IsRNull ω d a) : IsRNull ω d (c * a) :=
  isRNull_of_le a (fun i => Matrix.rank_mul_le_right _ _) ha

lemma isRNull_mul_right (c : MP d) {a : MP d} (ha : IsRNull ω d a) : IsRNull ω d (a * c) :=
  isRNull_of_le a (fun i => Matrix.rank_mul_le_left _ _) ha

lemma isRNull_sum {ι : Type*} (s : Finset ι) (a : ι → MP d) (ha : ∀ j ∈ s, IsRNull ω d (a j)) :
    IsRNull ω d (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isRNull_zero (ω := ω) (d := d))
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact isRNull_add (ha b (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

variable (ω d)

/-- the congruence "differ by a null sequence" -/
def rnullCon : RingCon (MP d) where
  r a b := IsRNull ω d (a - b)
  iseqv := ⟨fun a => by simpa using (isRNull_zero (ω := ω) (d := d)),
    fun {a b} h => by
      have := isRNull_neg h; rwa [neg_sub] at this,
    fun {a b c} h1 h2 => by
      have := isRNull_add h1 h2; rwa [sub_add_sub_cancel] at this⟩
  add' {a b c e} h1 h2 := by
    have := isRNull_add h1 h2
    have e1 : a - b + (c - e) = a + c - (b + e) := by abel
    rwa [e1] at this
  mul' {a b c e} h1 h2 := by
    have h := isRNull_add (isRNull_mul_left a h2) (isRNull_mul_right e h1)
    have e1 : a * (c - e) + (a - b) * e = a * c - b * e := by noncomm_ring
    rwa [e1] at h

/-- the rank ultraproduct -/
abbrev RU := (rnullCon ω d).Quotient

variable {ω d}

lemma mk_eq_iff (a b : MP d) :
    RingCon.mk' (rnullCon ω d) a = RingCon.mk' (rnullCon ω d) b ↔ IsRNull ω d (a - b) :=
  RingCon.eq _

end Null


section Main

variable {I : Type} {ω : Ultrafilter I} {d : I → ℕ}

/-- coordinatewise quasi-inverse -/
noncomputable def qP (a : MP d) : MP d := fun i => qinv (a i)

lemma qP_spec (a : MP d) : a * qP a * a = a := by
  funext i; exact qinv_spec (a i)

/-- an almost idempotent sequence is close to an exact idempotent -/
lemma idem_lift (F : MP d) (hF : IsRNull ω d (F * F - F)) :
    ∃ F' : MP d, F' * F' = F' ∧ IsRNull ω d (F' - F) := by
  set D := F * F - F with hD
  set B := qP D
  set e : MP d := 1 - B * D with he
  have hDe : D * e = 0 := by
    rw [he, mul_sub, mul_one, ← mul_assoc, qP_spec, sub_self]
  have hcomm : D * F = F * D := by rw [hD]; noncomm_ring
  have heFe : e * F * e = F * e := by
    have h1 : e * F * e = F * e - B * (D * F * e) := by rw [he]; noncomm_ring
    rw [h1, hcomm, mul_assoc F D e, hDe, mul_zero, mul_zero, sub_zero]
  refine ⟨F * e, ?_, ?_⟩
  · calc F * e * (F * e) = F * (e * F * e) := by noncomm_ring
      _ = F * (F * e) := by rw [heFe]
      _ = (D + F) * e := by rw [hD]; noncomm_ring
      _ = F * e := by rw [add_mul, hDe, zero_add]
  · have h : F * e - F = -(F * (B * D)) := by rw [he]; noncomm_ring
    rw [h]
    exact isRNull_neg (isRNull_mul_left F (isRNull_mul_left B hF))

/-- an almost incident element is close to an exactly incident one -/
lemma edge_lift (Fp Fq G : MP d) (h2 : IsRNull ω d (Fp * G - G)) (h3 : IsRNull ω d (Fq * G)) :
    ∃ a : MP d, Fp * a = a ∧ Fq * a = 0 ∧ IsRNull ω d (a - G) := by
  set h := Fp * G - G with hh
  set π1 : MP d := 1 - qP h * h with hπ1
  have hhπ : h * π1 = 0 := by rw [hπ1, mul_sub, mul_one, ← mul_assoc, qP_spec, sub_self]
  have hFG : Fp * (G * π1) = G * π1 := by
    have : Fp * (G * π1) = h * π1 + G * π1 := by rw [hh]; noncomm_ring
    rw [this, hhπ, zero_add]
  set h' := Fq * G * π1 with hh'
  have hn' : IsRNull ω d h' := isRNull_mul_right π1 h3
  set π2 : MP d := 1 - qP h' * h' with hπ2
  have hhπ2 : h' * π2 = 0 := by rw [hπ2, mul_sub, mul_one, ← mul_assoc, qP_spec, sub_self]
  refine ⟨G * π1 * π2, ?_, ?_, ?_⟩
  · rw [show Fp * (G * π1 * π2) = Fp * (G * π1) * π2 by noncomm_ring, hFG]
  · rw [show Fq * (G * π1 * π2) = h' * π2 by rw [hh']; noncomm_ring, hhπ2]
  · have e1 : G * π1 * π2 - G = -(G * (qP h * h) * π2) - G * (qP h' * h') := by
      rw [hπ1, hπ2]; noncomm_ring
    rw [e1]
    refine isRNull_sub (isRNull_neg (isRNull_mul_right π2 (isRNull_mul_left G
      (isRNull_mul_left _ ?_)))) (isRNull_mul_left G (isRNull_mul_left _ hn'))
    exact h2

end Main


section Final

variable {I : Type} {ω : Ultrafilter I} {d : I → ℕ}

lemma sqrt_lt_of_seven {q : ℝ} (hq : 7 ≤ q) : √q < (q + 1) / 3 := by
  have h0 : 0 ≤ q := by linarith
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith

/-- **No unital homomorphism.** The relations of `B` have no solution in a rank ultraproduct of
complex matrix rings. -/
theorem no_config {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (σ : P ≃ L) (hq : 7 ≤ order P L) (hd : ∀ i, 0 < d i)
    (f : P → RU ω d) (g : P → P → RU ω d) (x y : P → P → Fin 3 → RU ω d)
    (h1 : ∀ p, f p * f p = f p)
    (h2 : ∀ p p', p ∈ σ p' → f p * g p p' = g p p')
    (h3 : ∀ p p', p ∈ σ p' → f p' * g p p' = 0)
    (h4 : ∀ p p', p ∈ σ p' → ∑ i, y p p' i * g p p' * x p p' i = 1) : False := by
  classical
  have surj := RingCon.mk'_surjective (rnullCon ω d)
  choose F hF using fun p => surj (f p)
  choose G hG using fun p p' => surj (g p p')
  choose X hX using fun p p' i => surj (x p p' i)
  choose Y hY using fun p p' i => surj (y p p' i)
  have hF1 : ∀ p, IsRNull ω d (F p * F p - F p) := fun p => by
    rw [← mk_eq_iff, map_mul, hF, h1]
  have hF2 : ∀ p p', p ∈ σ p' → IsRNull ω d (F p * G p p' - G p p') := fun p p' h => by
    rw [← mk_eq_iff, map_mul, hF, hG, h2 p p' h]
  have hF3 : ∀ p p', p ∈ σ p' → IsRNull ω d (F p' * G p p') := fun p p' h => by
    have : IsRNull ω d (F p' * G p p' - 0) := by
      rw [← mk_eq_iff, map_mul, map_zero, hF, hG, h3 p p' h]
    rwa [sub_zero] at this
  have hF4 : ∀ p p', p ∈ σ p' →
      IsRNull ω d (∑ i, Y p p' i * G p p' * X p p' i - 1) := fun p p' h => by
    rw [← mk_eq_iff, map_sum, map_one]
    simp only [map_mul, hF, hG, hX, hY]
    exact h4 p p' h
  -- exact idempotents
  choose F' hF'1 hF'2 using fun p => idem_lift (F p) (hF1 p)
  -- exact incident elements
  have hex : ∀ p p', ∃ a : MP d, p ∈ σ p' →
      (F' p * a = a ∧ F' p' * a = 0 ∧ IsRNull ω d (a - G p p')) := by
    intro p p'
    by_cases h : p ∈ σ p'
    · have e2 : IsRNull ω d (F' p * G p p' - G p p') := by
        have : F' p * G p p' - G p p' = (F' p - F p) * G p p' + (F p * G p p' - G p p') := by
          noncomm_ring
        rw [this]
        exact isRNull_add (isRNull_mul_right _ (hF'2 p)) (hF2 p p' h)
      have e3 : IsRNull ω d (F' p' * G p p') := by
        have : F' p' * G p p' = (F' p' - F p') * G p p' + F p' * G p p' := by noncomm_ring
        rw [this]
        exact isRNull_add (isRNull_mul_right _ (hF'2 p')) (hF3 p p' h)
      obtain ⟨a, ha1, ha2, ha3⟩ := edge_lift (F' p) (F' p') (G p p') e2 e3
      exact ⟨a, fun _ => ⟨ha1, ha2, ha3⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose a ha using hex
  set r : P → P → MP d := fun p p' => a p p' * qP (a p p') with hr
  have hra : ∀ p p', r p p' * a p p' = a p p' := fun p p' => qP_spec _
  have hrr : ∀ p p', r p p' * r p p' = r p p' := fun p p' => by
    rw [hr]; simp only
    rw [← mul_assoc, qP_spec]
  -- the error terms
  set E : P → P → MP d := fun p p' => ∑ i, Y p p' i * a p p' * X p p' i - 1 with hE
  have hEn : ∀ p p', p ∈ σ p' → IsRNull ω d (E p p') := fun p p' h => by
    have : E p p' = ∑ i, Y p p' i * (a p p' - G p p') * X p p' i
        + (∑ i, Y p p' i * G p p' * X p p' i - 1) := by
      rw [hE]; simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; abel
    rw [this]
    refine isRNull_add (isRNull_sum _ _ fun i _ => ?_) (hF4 p p' h)
    exact isRNull_mul_right _ (isRNull_mul_left _ ((ha p p' h).2.2))
  -- constants
  set q : ℝ := (order P L : ℝ) with hqdef
  have hq7 : (7 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hgap := sqrt_lt_of_seven hq7
  set ε : ℝ := ((q + 1) / 3 - √q) / (4 * (q + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  -- a good coordinate
  have hev : ∀ᶠ i in (ω : Filter I), ∀ pp : P × P, pp.1 ∈ σ pp.2 →
      ((E pp.1 pp.2 i).rank : ℝ) / d i < ε := by
    rw [Filter.eventually_all]
    intro pp
    by_cases h : pp.1 ∈ σ pp.2
    · exact ((hEn pp.1 pp.2 h).eventually (gt_mem_nhds hεpos)).mono fun i hi _ => hi
    · exact Filter.Eventually.of_forall fun i h' => absurd h' h
  obtain ⟨i0, hi0⟩ := hev.exists
  have hd0 : (0 : ℝ) < d i0 := by exact_mod_cast hd i0
  -- rank of r at i0
  have hrank : ∀ p p', p ∈ σ p' → (1 - ε) * d i0 / 3 ≤ ((r p p' i0).rank : ℝ) := by
    intro p p' h
    have hsmall := hi0 (p, p') h
    rw [div_lt_iff₀ hd0] at hsmall
    have hdecomp : (1 : Matrix (Fin (d i0)) (Fin (d i0)) ℂ)
        = ∑ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0) - E p p' i0 := by
      have e1 : ∀ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0)
          = Y p p' i i0 * a p p' i0 * X p p' i i0 := by
        intro i
        have := congrFun (hra p p') i0
        simp only [Pi.mul_apply] at this
        rw [← mul_assoc, mul_assoc (Y p p' i i0), this]
      simp only [e1, hE, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Pi.one_apply]
      abel
    have hb1 : (d i0 : ℝ) ≤ ∑ i : Fin 3, ((r p p' i0).rank : ℝ) + (E p p' i0).rank := by
      have h1' : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) ℂ).rank : ℝ) = d i0 := by
        rw [Matrix.rank_one]; simp
      rw [← h1']
      have h2' : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) ℂ)).rank ≤
          (∑ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0)).rank + (E p p' i0).rank := by
        rw [hdecomp, sub_eq_add_neg]
        exact le_trans (rank_add_le' _ _) (by gcongr; exact rank_neg_le _)
      have h3' : (∑ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0)).rank
          ≤ ∑ i : Fin 3, (r p p' i0).rank := by
        refine le_trans (rank_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
      have : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) ℂ)).rank ≤
          ∑ i : Fin 3, (r p p' i0).rank + (E p p' i0).rank := le_trans h2' (by omega)
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb1
    norm_num at hb1
    nlinarith
  -- the inequality at i0
  have key := ineq_C σ (fun p => F' p i0) (fun p => congrFun (hF'1 p) i0)
    (fun p p' => r p p' i0) (fun p p' h => by
      refine ⟨congrFun (hrr p p') i0, ?_, ?_⟩
      · have : F' p * r p p' = r p p' := by
          rw [hr]; simp only; rw [← mul_assoc, (ha p p' h).1]
        exact congrFun this i0
      · have : F' p' * r p p' = 0 := by
          rw [hr]; simp only; rw [← mul_assoc, (ha p p' h).2.1, zero_mul]
        exact congrFun this i0)
  have htr : ∀ p p', p ∈ σ p' → ((1 - ε) * d i0 / 3) ≤ (r p p' i0).trace.re := by
    intro p p' h
    rw [trace_eq_rank_of_idem (congrFun (hrr p p') i0)]
    simpa using hrank p p' h
  have hlow : ∑ p', ∑ p, inc p (σ p') * ((1 - ε) * d i0 / 3)
      ≤ ∑ p', ∑ p, inc p (σ p') * (r p p' i0).trace.re := by
    refine Finset.sum_le_sum fun p' _ => Finset.sum_le_sum fun p _ => ?_
    unfold inc
    split_ifs with h
    · simpa using htr p p' h
    · simp
  have hcount : ∑ p' : P, ∑ p : P, inc p (σ p') * ((1 - ε) * d i0 / 3)
      = (q + 1) * Fintype.card P * ((1 - ε) * d i0 / 3) := by
    have hrow : ∀ p' : P, ∑ p : P, inc p (σ p') * ((1 - ε) * d i0 / 3)
        = (q + 1) * ((1 - ε) * d i0 / 3) := fun p' => by
      rw [← Finset.sum_mul, sum_inc_point (σ p')]
    rw [Finset.sum_congr rfl fun p' _ => hrow p', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Fintype.card_fin] at key
  have hP : (0 : ℝ) < Fintype.card P := by
    have : Nonempty P := by
      obtain ⟨p, -⟩ := @ProjectivePlane.exists_config P L _ _
      exact ⟨p⟩
    exact_mod_cast Fintype.card_pos
  have hfinal : 4 * ((q + 1) * Fintype.card P * ((1 - ε) * d i0 / 3))
      ≤ ((q + 1) + √q) * Fintype.card P * d i0 := by
    rw [← hcount]; linarith
  have hε' : 4 * (q + 1) * ε = (q + 1) / 3 - √q := by
    rw [hε]; field_simp
  have hcontra : ((q + 1) + √q) * Fintype.card P * d i0
      < 4 * ((q + 1) * Fintype.card P * ((1 - ε) * d i0 / 3)) := by
    have hpos : 0 < (Fintype.card P : ℝ) * d i0 := mul_pos hP hd0
    have : (q + 1) + √q < 4 * (q + 1) * (1 - ε) / 3 := by nlinarith
    nlinarith
  linarith

end Final

end RankRings

end

import RankRings.Ineq
import RankRings.SRank

/-! All fields of characteristic zero: the relations of `B_l`
have no solution in a rank ultraproduct of matrix rings `M_{d i}(F i)` over arbitrary fields
`F i` of characteristic zero. At one good coordinate the finitely many matrices involved have
entries in a countable subfield, which embeds into `ℂ`; there `ineq_C` applies. -/

open Matrix Configuration Configuration.ProjectivePlane Cardinal

namespace RankRings
namespace Gen

section Basic

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- every matrix over a field has a quasi-inverse -/
lemma exists_qinv (A : Matrix n n K) : ∃ B : Matrix n n K, A * B * A = A := by
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

noncomputable def qinv (A : Matrix n n K) : Matrix n n K := (exists_qinv A).choose

lemma qinv_spec (A : Matrix n n K) : A * qinv A * A = A := (exists_qinv A).choose_spec

/-- the trace of an idempotent matrix is its rank, cast into the field -/
lemma trace_eq_rank_of_idem {A : Matrix n n K} (h : A * A = A) : A.trace = (A.rank : K) := by
  have he : IsIdempotentElem (Matrix.toLin' A) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K n), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at h1
  rw [h1, Matrix.rank]
  rfl

omit [DecidableEq n] in
lemma rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix n n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le' _ _) (by omega)

end Basic


section Embed

/-- a countable subset of a field of characteristic zero lies in a subfield that embeds into `ℂ` -/
theorem exists_embed {K : Type} [Field K] [CharZero K] (S : Set K) (hS : S.Countable) :
    ∃ (K0 : Subfield K) (_ : K0 →+* ℂ), S ⊆ K0 := by
  set K0 := Subfield.closure S with hK0def
  have hK0 : #K0 ≤ ℵ₀ := by
    refine (Subfield.cardinalMk_closure_le_max S).trans (max_le ?_ le_rfl)
    exact Cardinal.le_aleph0_iff_set_countable.mpr hS
  have : CharZero K0 := K0.subtype.charZero
  let R := MvPolynomial ℝ K0
  let Fr := FractionRing R
  let L := AlgebraicClosure Fr
  have hR : #R = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real]
    apply le_antisymm
    · exact sup_le (sup_le (hK0.trans aleph0_le_continuum) le_rfl) aleph0_le_continuum
    · exact le_sup_of_le_left le_sup_right
  have hFr : #Fr = 𝔠 := by
    rw [IsFractionRing.cardinalMk R Fr, hR]
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · have h := Algebra.IsAlgebraic.cardinalMk_le_max Fr L
      rw [hFr, max_eq_left aleph0_le_continuum] at h
      exact h
    · rw [← hFr]
      exact mk_le_of_injective (algebraMap Fr L).injective
  let ψ : K0 →+* L := (algebraMap Fr L).comp ((algebraMap R Fr).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff ψ.injective).mp inferInstance
  obtain ⟨e⟩ : Nonempty (L ≃+* ℂ) := by
    apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [hL]; exact aleph0_lt_continuum
    · rw [← Cardinal.eq, hL, Cardinal.mk_complex]
  exact ⟨K0, e.toRingHom.comp ψ, Subfield.subset_closure⟩

end Embed


section Null

variable {I : Type} (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]

/-- sequences of matrices of sizes `d i` over the fields `F i` -/
abbrev MPF := ∀ i, Matrix (Fin (d i)) (Fin (d i)) (F i)

/-- normalized rank tends to `0` along `ω` -/
def IsRNull (a : MPF d F) : Prop :=
  Filter.Tendsto (fun i => ((a i).rank : ℝ) / d i) (ω : Filter I) (nhds 0)

variable {ω d F}

lemma isRNull_of_le {a : MPF d F} (b : MPF d F) (h : ∀ i, (a i).rank ≤ (b i).rank)
    (hb : IsRNull ω d F b) : IsRNull ω d F a := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun i => ?_) (fun i => ?_)
  · positivity
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (h i)) (by positivity)

lemma isRNull_of_le_add {a : MPF d F} (b c : MPF d F)
    (h : ∀ i, (a i).rank ≤ (b i).rank + (c i).rank)
    (hb : IsRNull ω d F b) (hc : IsRNull ω d F c) : IsRNull ω d F a := by
  have hbc := hb.add hc
  rw [add_zero] at hbc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbc (fun i => ?_) (fun i => ?_)
  · positivity
  · simp only
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h i) (by positivity)

lemma isRNull_zero : IsRNull ω d F 0 := by
  unfold IsRNull
  simp only [Pi.zero_apply, Matrix.rank_zero, Nat.cast_zero, zero_div]
  exact tendsto_const_nhds

lemma isRNull_add {a b : MPF d F} (ha : IsRNull ω d F a) (hb : IsRNull ω d F b) :
    IsRNull ω d F (a + b) :=
  isRNull_of_le_add a b (fun i => rank_add_le' _ _) ha hb

lemma isRNull_neg {a : MPF d F} (ha : IsRNull ω d F a) : IsRNull ω d F (-a) :=
  isRNull_of_le a (fun i => rank_neg_le _) ha

lemma isRNull_sub {a b : MPF d F} (ha : IsRNull ω d F a) (hb : IsRNull ω d F b) :
    IsRNull ω d F (a - b) := by
  rw [sub_eq_add_neg]; exact isRNull_add ha (isRNull_neg hb)

lemma isRNull_mul_left (c : MPF d F) {a : MPF d F} (ha : IsRNull ω d F a) :
    IsRNull ω d F (c * a) :=
  isRNull_of_le a (fun i => Matrix.rank_mul_le_right _ _) ha

lemma isRNull_mul_right (c : MPF d F) {a : MPF d F} (ha : IsRNull ω d F a) :
    IsRNull ω d F (a * c) :=
  isRNull_of_le a (fun i => Matrix.rank_mul_le_left _ _) ha

lemma isRNull_sum {ι : Type*} (s : Finset ι) (a : ι → MPF d F) (ha : ∀ j ∈ s, IsRNull ω d F (a j)) :
    IsRNull ω d F (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isRNull_zero (ω := ω) (d := d) (F := F))
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact isRNull_add (ha b (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

variable (ω d F)

/-- the congruence "differ by a null sequence" -/
def rnullCon : RingCon (MPF d F) where
  r a b := IsRNull ω d F (a - b)
  iseqv := ⟨fun a => by simpa using (isRNull_zero (ω := ω) (d := d) (F := F)),
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

/-- the rank ultraproduct of `M_{d i}(F i)` -/
abbrev RUF := (rnullCon ω d F).Quotient

variable {ω d F}

lemma mk_eq_iff (a b : MPF d F) :
    RingCon.mk' (rnullCon ω d F) a = RingCon.mk' (rnullCon ω d F) b ↔ IsRNull ω d F (a - b) :=
  RingCon.eq _

end Null


section Main

variable {I : Type} {ω : Ultrafilter I} {d : I → ℕ} {F : I → Type} [∀ i, Field (F i)]

/-- coordinatewise quasi-inverse -/
noncomputable def qP (a : MPF d F) : MPF d F := fun i => qinv (a i)

lemma qP_spec (a : MPF d F) : a * qP a * a = a := by
  funext i; exact qinv_spec (a i)

lemma idem_lift (A : MPF d F) (hA : IsRNull ω d F (A * A - A)) :
    ∃ A' : MPF d F, A' * A' = A' ∧ IsRNull ω d F (A' - A) := by
  set D := A * A - A with hD
  set B := qP D
  set e : MPF d F := 1 - B * D with he
  have hDe : D * e = 0 := by
    rw [he, mul_sub, mul_one, ← mul_assoc, qP_spec, sub_self]
  have hcomm : D * A = A * D := by rw [hD]; noncomm_ring
  have heAe : e * A * e = A * e := by
    have h1 : e * A * e = A * e - B * (D * A * e) := by rw [he]; noncomm_ring
    rw [h1, hcomm, mul_assoc A D e, hDe, mul_zero, mul_zero, sub_zero]
  refine ⟨A * e, ?_, ?_⟩
  · calc A * e * (A * e) = A * (e * A * e) := by noncomm_ring
      _ = A * (A * e) := by rw [heAe]
      _ = (D + A) * e := by rw [hD]; noncomm_ring
      _ = A * e := by rw [add_mul, hDe, zero_add]
  · have h : A * e - A = -(A * (B * D)) := by rw [he]; noncomm_ring
    rw [h]
    exact isRNull_neg (isRNull_mul_left A (isRNull_mul_left B hA))

lemma edge_lift (Fp Fq G : MPF d F) (h2 : IsRNull ω d F (Fp * G - G))
    (h3 : IsRNull ω d F (Fq * G)) :
    ∃ a : MPF d F, Fp * a = a ∧ Fq * a = 0 ∧ IsRNull ω d F (a - G) := by
  set h := Fp * G - G with hh
  set π1 : MPF d F := 1 - qP h * h with hπ1
  have hhπ : h * π1 = 0 := by rw [hπ1, mul_sub, mul_one, ← mul_assoc, qP_spec, sub_self]
  have hFG : Fp * (G * π1) = G * π1 := by
    have : Fp * (G * π1) = h * π1 + G * π1 := by rw [hh]; noncomm_ring
    rw [this, hhπ, zero_add]
  set h' := Fq * G * π1 with hh'
  have hn' : IsRNull ω d F h' := isRNull_mul_right π1 h3
  set π2 : MPF d F := 1 - qP h' * h' with hπ2
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


section Transfer

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- a matrix whose entries lie in a subfield, as a matrix over the subfield -/
def lift0 (K0 : Subfield K) (A : Matrix n n K) (h : ∀ a b, A a b ∈ K0) : Matrix n n K0 :=
  Matrix.of fun a b => ⟨A a b, h a b⟩

omit [Fintype n] [DecidableEq n] in
lemma lift0_map (K0 : Subfield K) (A : Matrix n n K) (h : ∀ a b, A a b ∈ K0) :
    (lift0 K0 A h).map K0.subtype = A := by
  ext a b; rfl

lemma transfer_mul {K0 : Subfield K} (φ : K0 →+* ℂ) {A B C : Matrix n n K0}
    (h : A.map K0.subtype * B.map K0.subtype = C.map K0.subtype) :
    A.map φ * B.map φ = C.map φ := by
  have hABC : A * B = C := by
    apply Matrix.map_injective (f := K0.subtype) Subtype.val_injective
    show (A * B).map K0.subtype = C.map K0.subtype
    rw [Matrix.map_mul]; exact h
  rw [← Matrix.map_mul, hABC]

lemma trace_transfer {K0 : Subfield K} (φ : K0 →+* ℂ) {A : Matrix n n K0}
    (h : A.map K0.subtype * A.map K0.subtype = A.map K0.subtype) :
    (A.map φ).trace = ((A.map K0.subtype).rank : ℂ) := by
  have h1 := trace_eq_rank_of_idem h
  rw [← AddMonoidHom.map_trace K0.subtype] at h1
  have h2 : A.trace = ((A.map K0.subtype).rank : K0) := by
    apply Subtype.val_injective
    rw [show A.trace.val = K0.subtype A.trace from rfl, h1]
    simp
  rw [← AddMonoidHom.map_trace φ, h2, map_natCast]

end Transfer


section Final

variable {I : Type} {ω : Ultrafilter I} {d : I → ℕ} {F : I → Type} [∀ i, Field (F i)]
  [∀ i, CharZero (F i)]

lemma sqrt_lt_of_seven {q : ℝ} (hq : 7 ≤ q) : √q < (q + 1) / 3 := by
  have h0 : 0 ≤ q := by linarith
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith

/-- **No unital homomorphism, any fields of characteristic zero.** The relations of `B` have no
solution in a rank ultraproduct of matrix rings `M_{d i}(F i)`, `F i` fields of characteristic 0. -/
theorem no_config {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (σ : P ≃ L) (hq : 7 ≤ order P L) (hd : ∀ i, 0 < d i)
    (f : P → RUF ω d F) (g : P → P → RUF ω d F) (x y : P → P → Fin 3 → RUF ω d F)
    (h1 : ∀ p, f p * f p = f p)
    (h2 : ∀ p p', p ∈ σ p' → f p * g p p' = g p p')
    (h3 : ∀ p p', p ∈ σ p' → f p' * g p p' = 0)
    (h4 : ∀ p p', p ∈ σ p' → ∑ i, y p p' i * g p p' * x p p' i = 1) : False := by
  classical
  have surj := RingCon.mk'_surjective (rnullCon ω d F)
  choose Fm hF using fun p => surj (f p)
  choose G hG using fun p p' => surj (g p p')
  choose X hX using fun p p' i => surj (x p p' i)
  choose Y hY using fun p p' i => surj (y p p' i)
  have hF1 : ∀ p, IsRNull ω d F (Fm p * Fm p - Fm p) := fun p => by
    rw [← mk_eq_iff, map_mul, hF, h1]
  have hF2 : ∀ p p', p ∈ σ p' → IsRNull ω d F (Fm p * G p p' - G p p') := fun p p' h => by
    rw [← mk_eq_iff, map_mul, hF, hG, h2 p p' h]
  have hF3 : ∀ p p', p ∈ σ p' → IsRNull ω d F (Fm p' * G p p') := fun p p' h => by
    have : IsRNull ω d F (Fm p' * G p p' - 0) := by
      rw [← mk_eq_iff, map_mul, map_zero, hF, hG, h3 p p' h]
    rwa [sub_zero] at this
  have hF4 : ∀ p p', p ∈ σ p' →
      IsRNull ω d F (∑ i, Y p p' i * G p p' * X p p' i - 1) := fun p p' h => by
    rw [← mk_eq_iff, map_sum, map_one]
    simp only [map_mul, hF, hG, hX, hY]
    exact h4 p p' h
  -- exact idempotents
  choose F' hF'1 hF'2 using fun p => idem_lift (Fm p) (hF1 p)
  -- exact incident elements
  have hex : ∀ p p', ∃ a : MPF d F, p ∈ σ p' →
      (F' p * a = a ∧ F' p' * a = 0 ∧ IsRNull ω d F (a - G p p')) := by
    intro p p'
    by_cases h : p ∈ σ p'
    · have e2 : IsRNull ω d F (F' p * G p p' - G p p') := by
        have : F' p * G p p' - G p p' = (F' p - Fm p) * G p p' + (Fm p * G p p' - G p p') := by
          noncomm_ring
        rw [this]
        exact isRNull_add (isRNull_mul_right _ (hF'2 p)) (hF2 p p' h)
      have e3 : IsRNull ω d F (F' p' * G p p') := by
        have : F' p' * G p p' = (F' p' - Fm p') * G p p' + Fm p' * G p p' := by noncomm_ring
        rw [this]
        exact isRNull_add (isRNull_mul_right _ (hF'2 p')) (hF3 p p' h)
      obtain ⟨a, ha1, ha2, ha3⟩ := edge_lift (F' p) (F' p') (G p p') e2 e3
      exact ⟨a, fun _ => ⟨ha1, ha2, ha3⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose a ha using hex
  set r : P → P → MPF d F := fun p p' => a p p' * qP (a p p') with hr
  have hra : ∀ p p', r p p' * a p p' = a p p' := fun p p' => qP_spec _
  have hrr : ∀ p p', r p p' * r p p' = r p p' := fun p p' => by
    rw [hr]; simp only
    rw [← mul_assoc, qP_spec]
  -- the error terms
  set E : P → P → MPF d F := fun p p' => ∑ i, Y p p' i * a p p' * X p p' i - 1 with hE
  have hEn : ∀ p p', p ∈ σ p' → IsRNull ω d F (E p p') := fun p p' h => by
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
    have hdecomp : (1 : Matrix (Fin (d i0)) (Fin (d i0)) (F i0))
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
      have h1' : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) (F i0)).rank : ℝ) = d i0 := by
        rw [Matrix.rank_one]; simp
      rw [← h1']
      have h2' : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) (F i0))).rank ≤
          (∑ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0)).rank
            + (E p p' i0).rank := by
        rw [hdecomp, sub_eq_add_neg]
        exact le_trans (rank_add_le' _ _) (by gcongr; exact rank_neg_le _)
      have h3' : (∑ i, (Y p p' i i0 * r p p' i0) * (a p p' i0 * X p p' i i0)).rank
          ≤ ∑ i : Fin 3, (r p p' i0).rank := by
        refine le_trans (rank_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
      have : ((1 : Matrix (Fin (d i0)) (Fin (d i0)) (F i0))).rank ≤
          ∑ i : Fin 3, (r p p' i0).rank + (E p p' i0).rank := le_trans h2' (by omega)
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb1
    norm_num at hb1
    nlinarith
  -- transfer to ℂ at i0: a countable subfield containing all entries embeds into ℂ
  set S : Set (F i0) :=
    Set.range (fun t : P × Fin (d i0) × Fin (d i0) => F' t.1 i0 t.2.1 t.2.2) ∪
    Set.range (fun t : P × P × Fin (d i0) × Fin (d i0) => r t.1 t.2.1 i0 t.2.2.1 t.2.2.2)
    with hSdef
  have hSc : S.Countable := (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨K0, φ, hSK⟩ := exists_embed S hSc
  have memF : ∀ p a b, F' p i0 a b ∈ K0 := fun p a b => hSK (Or.inl ⟨(p, a, b), rfl⟩)
  have memR : ∀ p p' a b, r p p' i0 a b ∈ K0 := fun p p' a b =>
    hSK (Or.inr ⟨(p, p', a, b), rfl⟩)
  have hF0 : ∀ p, (lift0 K0 (F' p i0) (memF p)).map K0.subtype = F' p i0 :=
    fun p => lift0_map _ _ _
  have hR0 : ∀ p p', (lift0 K0 (r p p' i0) (memR p p')).map K0.subtype = r p p' i0 :=
    fun p p' => lift0_map _ _ _
  have key := ineq_C σ (fun p => (lift0 K0 (F' p i0) (memF p)).map φ)
    (fun p => transfer_mul φ (by rw [hF0]; exact congrFun (hF'1 p) i0))
    (fun p p' => (lift0 K0 (r p p' i0) (memR p p')).map φ) (fun p p' h => by
      refine ⟨transfer_mul φ (by rw [hR0]; exact congrFun (hrr p p') i0),
        transfer_mul φ ?_, ?_⟩
      · rw [hF0, hR0]
        have : F' p * r p p' = r p p' := by
          rw [hr]; simp only; rw [← mul_assoc, (ha p p' h).1]
        exact congrFun this i0
      · have h0 := transfer_mul φ (A := lift0 K0 (F' p' i0) (memF p'))
          (B := lift0 K0 (r p p' i0) (memR p p')) (C := 0) (by
            rw [hF0, hR0, Matrix.map_zero _ (map_zero _)]
            have : F' p' * r p p' = 0 := by
              rw [hr]; simp only; rw [← mul_assoc, (ha p p' h).2.1, zero_mul]
            exact congrFun this i0)
        rwa [Matrix.map_zero _ (map_zero φ)] at h0)
  have htr : ∀ p p', p ∈ σ p' → ((1 - ε) * d i0 / 3) ≤
      ((lift0 K0 (r p p' i0) (memR p p')).map φ).trace.re := by
    intro p p' h
    rw [trace_transfer φ (by rw [hR0]; exact congrFun (hrr p p') i0), hR0]
    simpa using hrank p p' h
  have hlow : ∑ p', ∑ p, inc p (σ p') * ((1 - ε) * d i0 / 3)
      ≤ ∑ p', ∑ p, inc p (σ p') * ((lift0 K0 (r p p' i0) (memR p p')).map φ).trace.re := by
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
    rw [Finset.sum_congr rfl fun p' _ => hrow p', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
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

end Gen
end RankRings

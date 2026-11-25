import RankRings.RankFn
import RankRings.Exotic

/-!
# The exotic configuration in the rank algebra over an `l`-adic field
-/

open Matrix Filter
open scoped LinearAlgebra.Projectivization

namespace RankRings

variable {l : ℕ} [Fact l.Prime]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[l] K]

set_option linter.unusedSectionVars false

/-- The ring map `ℤ_[l] → K`. -/
noncomputable def phi (l : ℕ) [Fact l.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[l] K] :
    ℤ_[l] →+* K :=
  (algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom

lemma norm_phi (x : ℤ_[l]) : ‖phi l K x‖ = ‖x‖ := by
  show ‖algebraMap ℚ_[l] K (x : ℚ_[l])‖ = ‖x‖
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

/-- index types -/
abbrev WI (k : ℕ) : Type := Word (3 * k + 1)

lemma card_WI (k : ℕ) : Fintype.card (WI k) = 3 ^ (3 * k + 1) := by
  simp [WI, Word]

/-- An integral matrix sequence gives a tight sequence. -/
lemma isTight_map {ω : Ultrafilter ℕ} (A : ∀ k, Matrix (WI k) (WI k) ℤ_[l]) :
    IsTight ω (fun k => (A k).map (phi l K) : Seq WI K) :=
  isTight_of_bdd fun k i j => by
    rw [map_apply, norm_phi]; exact PadicInt.norm_le_one _

lemma rank_map_dg {m : ℕ} (W : Finset (Word m)) :
    ((dg W : Matrix (Word m) (Word m) ℤ_[l]).map (phi l K)).rank ≤ W.card := by
  classical
  have e : (dg W : Matrix (Word m) (Word m) ℤ_[l]).map (phi l K)
      = diagonal fun w => if w ∈ W then (1 : K) else 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; by_cases h : i ∈ W <;> simp [dg, h]
    · simp [dg, hij]
  rw [e, rank_diagonal]
  apply le_of_eq
  rw [Fintype.card_subtype]
  congr 1
  ext w; simp

/-- The approximate relations of `exotic` give null sequences. -/
lemma isNull_of_approx {ω : Ultrafilter ℕ} (hω : ∀ j : ℕ, ∀ᶠ k in (ω : Filter ℕ), j ≤ k)
    (E : ∀ k, Matrix (WI k) (WI k) ℤ_[l])
    (h : ∀ t : ℕ, ∀ δ : ℝ, 0 < δ → ∃ K0 : ℕ, ∀ k ≥ K0,
      ∃ Q Rm Z : Matrix (WI k) (WI k) ℤ_[l], ∃ W : Finset (WI k),
        E k = (l : ℤ_[l]) ^ t • Q + Rm * dg W * Z ∧ (W.card : ℝ) ≤ δ * 3 ^ (3 * k + 1)) :
    IsNull ω (fun k => (E k).map (phi l K) : Seq WI K) := by
  intro ε hε r hr
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hl)
  obtain ⟨K0, hK0⟩ := h t ε hε
  filter_upwards [hω K0] with k hk
  obtain ⟨Q, Rm, Z, W, hE, hW⟩ := hK0 k hk
  unfold uu
  rw [card_WI, Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ (by positivity)]
  have h1 : srk r ((E k).map (phi l K)) ≤ W.card := by
    refine (srk_le (A' := (Rm * dg W * Z).map (phi l K)) fun i j => ?_).trans ?_
    · rw [hE, Matrix.map_add _ (map_add _), Matrix.add_apply, add_sub_cancel_right, map_apply, Matrix.smul_apply,
        smul_eq_mul, norm_phi, norm_mul, norm_pow, PadicInt.norm_p]
      calc ((l : ℝ)⁻¹) ^ t * ‖Q i j‖ ≤ ((l : ℝ)⁻¹) ^ t * 1 := by
            gcongr; exact PadicInt.norm_le_one _
        _ ≤ r := by rw [mul_one]; exact ht.le
    · rw [Matrix.map_mul, Matrix.map_mul]
      exact (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans (rank_map_dg (l := l) (K := K) W))
  calc (srk r ((E k).map (phi l K)) : ℝ) ≤ W.card := by exact_mod_cast h1
    _ ≤ ε * 3 ^ (3 * k + 1) := hW

variable (l K) in
/-- From integral sequences to the rank algebra. -/
noncomputable def Ψ (ω : Ultrafilter ℕ) : (∀ k, Matrix (WI k) (WI k) ℤ_[l]) →+* tight K WI ω :=
  RingHom.codRestrict (RingHom.pi fun k => ((phi l K).mapMatrix).comp (Pi.evalRingHom _ k))
    (tight K WI ω) (fun A => isTight_map A)

variable (l K) in
noncomputable def Θ (ω : Ultrafilter ℕ) : (∀ k, Matrix (WI k) (WI k) ℤ_[l]) →+* RR K WI ω :=
  (RingCon.mk' _).comp (Ψ l K ω)

lemma Ψ_val {ω : Ultrafilter ℕ} (A : ∀ k, Matrix (WI k) (WI k) ℤ_[l]) :
    ((Ψ l K ω A : tight K WI ω) : Seq WI K) = fun k => (A k).map (phi l K) := rfl

lemma Θ_eq_iff {ω : Ultrafilter ℕ} (A B : ∀ k, Matrix (WI k) (WI k) ℤ_[l]) :
    Θ l K ω A = Θ l K ω B ↔ IsNull ω (fun k => (A k - B k).map (phi l K) : Seq WI K) := by
  show ((Ψ l K ω A : tight K WI ω) : RR K WI ω) = ((Ψ l K ω B : tight K WI ω) : RR K WI ω) ↔ _
  rw [coe_eq_coe]
  have : ((Ψ l K ω A : tight K WI ω) : Seq WI K) - ((Ψ l K ω B : tight K WI ω) : Seq WI K)
      = (fun k => (A k - B k).map (phi l K)) := by
    rw [Ψ_val, Ψ_val]
    funext k
    rw [Pi.sub_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      map_sub]
  rw [this]

/-- **The exotic configuration in the rank algebra.** -/
theorem exotic_RR (l : ℕ) [Fact l.Prime] (K : Type*) [NormedField K] [IsUltrametricDist K]
    [NormedAlgebra ℚ_[l] K] (ω : Ultrafilter ℕ) (hω : ∀ j : ℕ, ∀ᶠ k in (ω : Filter ℕ), j ≤ k)
    (σ : ℙ (ZMod l) (Fin 3 → ZMod l) ≃ ℙ (ZMod l) (Fin 3 → ZMod l)) (hσ : ∀ p, p ∉ σ p) :
    ∃ (f : ℙ (ZMod l) (Fin 3 → ZMod l) → RR K WI ω)
      (g : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) → RR K WI ω)
      (x y : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) → Fin 3 → RR K WI ω),
      (∀ p, f p * f p = f p) ∧
      (∀ p p', p ∈ σ p' → f p * g p p' = g p p') ∧
      (∀ p p', p ∈ σ p' → f p' * g p p' = 0) ∧
      (∀ p p', p ∈ σ p' → ∑ i, y p p' i * g p p' * x p p' i = 1) := by
  obtain ⟨F, G, X, Y, h1, h2, h3⟩ := exotic l σ hσ
  refine ⟨fun p => Θ l K ω (F p), fun p p' => Θ l K ω (G p p'),
    fun p p' i => Θ l K ω (X p p' i), fun p p' i => Θ l K ω (Y p p' i), ?_, ?_, ?_, ?_⟩
  · intro p
    rw [← map_mul]
    congr 1
    funext k
    exact h1 p k
  · intro p p' hpp
    rw [← map_mul, Θ_eq_iff]
    have := isNull_neg (isNull_of_approx (K := K) (ω := ω) hω
      (fun k => (1 - F p k) * G p p' k) (fun t δ hδ => by
        obtain ⟨K0, hK0⟩ := (h3 p p' hpp) t δ hδ
        exact ⟨K0, fun k hk => (hK0 k hk).1⟩))
    convert this using 1
    funext k
    show (F p k * G p p' k - G p p' k).map (phi l K) = -(((1 - F p k) * G p p' k).map (phi l K))
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_neg]
    congr 1
    noncomm_ring
  · intro p p' hpp
    rw [← map_mul, ← map_zero (Θ l K ω), Θ_eq_iff]
    have := isNull_of_approx (K := K) (ω := ω) hω
      (fun k => F p' k * G p p' k) (fun t δ hδ => by
        obtain ⟨K0, hK0⟩ := (h3 p p' hpp) t δ hδ
        exact ⟨K0, fun k hk => (hK0 k hk).2⟩)
    convert this using 1
    funext k
    simp
  · intro p p' hpp
    have e : ∑ i, Θ l K ω (Y p p' i) * Θ l K ω (G p p') * Θ l K ω (X p p' i)
        = Θ l K ω (∑ i, Y p p' i * G p p' * X p p' i) := by
      rw [map_sum]
      simp only [map_mul]
    rw [e, ← map_one (Θ l K ω)]
    congr 1
    funext k
    rw [Finset.sum_apply]
    simpa using h2 p p' hpp k

end RankRings

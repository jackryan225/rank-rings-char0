module

public import Mathlib

@[expose] public section
/-! Geometric inputs. Mathlib only.
`exists_sigma`: a bijection from points to lines with `p ∉ σ p` (Hall's theorem);
`exists_beta`, `exists_alpha`: adapted bases over a field;
`order_ofField`: the plane over `ZMod l` has order `l`. -/

open Finset Matrix
open scoped LinearAlgebra.Projectivization

namespace RankRings

section sigma

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]

open Configuration Configuration.ProjectivePlane

open scoped Classical in
theorem card_not_mem_lines (p : P) :
    #(univ.filter fun l : L => p ∉ l) = Fintype.card L - (order P L + 1) := by
  classical
  have h1 : #(univ.filter fun l : L => p ∈ l) = order P L + 1 := by
    rw [← lineCount_eq L p, lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset L))
    (p := fun l : L => p ∈ l)
  rw [Finset.card_univ] at h2
  omega

open scoped Classical in
theorem card_not_mem_points (l : L) :
    #(univ.filter fun p : P => p ∉ l) = Fintype.card P - (order P L + 1) := by
  classical
  have h1 : #(univ.filter fun p : P => p ∈ l) = order P L + 1 := by
    rw [← pointCount_eq P l, pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset P))
    (p := fun p : P => p ∈ l)
  rw [Finset.card_univ] at h2
  omega

theorem exists_sigma : ∃ σ : P ≃ L, ∀ p, p ∉ σ p := by
  classical
  set q := order P L
  set d := Fintype.card L - (q + 1) with hd
  have hcardP : Fintype.card P = q ^ 2 + q + 1 := card_points P L
  have hcardL : Fintype.card L = q ^ 2 + q + 1 := card_lines P L
  have hq : 1 < q := one_lt_order P L
  have hdpos : 0 < d := by
    rw [hd, hcardL]
    have : q + 1 < q ^ 2 + q + 1 := by nlinarith
    omega
  let t : P → Finset L := fun p => univ.filter fun l : L => p ∉ l
  have hall : ∀ S : Finset P, #S ≤ #(S.biUnion t) := by
    intro S
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := S) (t := S.biUnion t) (r := fun p l => p ∉ l)
    have habove : ∀ p ∈ S, #((S.biUnion t).bipartiteAbove (fun p l => p ∉ l) p) = d := by
      intro p hp
      have : (S.biUnion t).bipartiteAbove (fun p l => p ∉ l) p = t p := by
        ext l
        simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_biUnion, t,
          Finset.mem_univ, true_and]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨⟨p, hp, h⟩, h⟩
      rw [this]
      convert card_not_mem_lines (L := L) p
    have hbelow : ∀ l ∈ S.biUnion t, #(S.bipartiteBelow (fun p l => p ∉ l) l) ≤ d := by
      intro l _
      have h : #(univ.filter fun p : P => p ∉ l) = d := by
        have e : Fintype.card L = Fintype.card P := hcardL.trans hcardP.symm
        rw [hd, e]
        convert card_not_mem_points (P := P) l
      calc #(S.bipartiteBelow (fun p l => p ∉ l) l) ≤ #(univ.filter fun p : P => p ∉ l) := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.bipartiteBelow, Finset.mem_filter] at hp
            simp [hp.2]
        _ = d := h
    rw [Finset.sum_congr rfl habove] at hdc
    have hle : ∑ l ∈ S.biUnion t, #(S.bipartiteBelow (fun p l => p ∉ l) l)
        ≤ ∑ _l ∈ S.biUnion t, d := Finset.sum_le_sum hbelow
    rw [← hdc, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hle
    exact Nat.le_of_mul_le_mul_right hle hdpos
  obtain ⟨f, hfi, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hfi, by rw [hcardP, hcardL]⟩
  refine ⟨Equiv.ofBijective f hbij, fun p => ?_⟩
  have := hft p
  simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

end sigma

section bases

variable {k : Type*} [Field k]

/-- extend a nonzero vector to an invertible matrix with this first column -/
theorem exists_extend (v : Fin 3 → k) (hv : v ≠ 0) :
    ∃ γ γ' : Matrix (Fin 3) (Fin 3) k, γ * γ' = 1 ∧ γ' * γ = 1 ∧ ∀ i, γ i 0 = v i := by
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hr
  have key : ∀ γ : Matrix (Fin 3) (Fin 3) k, γ.det ≠ 0 → (∀ i, γ i 0 = v i) →
      ∃ γ γ' : Matrix (Fin 3) (Fin 3) k, γ * γ' = 1 ∧ γ' * γ = 1 ∧ ∀ i, γ i 0 = v i := by
    intro γ hdet hcol
    have hu : IsUnit γ.det := isUnit_iff_ne_zero.mpr hdet
    exact ⟨γ, γ⁻¹, Matrix.mul_nonsing_inv γ hu, Matrix.nonsing_inv_mul γ hu, hcol⟩
  fin_cases r
  · refine key !![v 0, 0, 0; v 1, 1, 0; v 2, 0, 1] ?_ ?_
    · simpa [Matrix.det_fin_three] using hr
    · intro i; fin_cases i <;> rfl
  · refine key !![v 0, 1, 0; v 1, 0, 0; v 2, 0, 1] ?_ ?_
    · simpa [Matrix.det_fin_three] using hr
    · intro i; fin_cases i <;> rfl
  · refine key !![v 0, 1, 0; v 1, 0, 1; v 2, 0, 0] ?_ ?_
    · simpa [Matrix.det_fin_three] using hr
    · intro i; fin_cases i <;> rfl

theorem exists_beta (v u : Fin 3 → k) (h : u ⬝ᵥ v ≠ 0) :
    ∃ β β' : Matrix (Fin 3) (Fin 3) k, β * β' = 1 ∧ β' * β = 1 ∧ (∀ i, β i 0 = v i) ∧
      (∀ j, j ≠ 0 → u ⬝ᵥ (fun i => β i j) = 0) := by
  have hv : v ≠ 0 := by rintro rfl; simp at h
  obtain ⟨γ, γ', h1, h2, hc⟩ := exists_extend v hv
  set d : Fin 3 → k := fun j => u ⬝ᵥ (fun i => γ i j) with hdd
  have hd0 : d 0 = u ⬝ᵥ v := by
    simp only [hdd]; congr 1; funext i; exact hc i
  set c := d 0
  have hc0 : c ≠ 0 := by rw [hd0]; exact h
  set E : Matrix (Fin 3) (Fin 3) k := !![1, -(d 1 / c), -(d 2 / c); 0, 1, 0; 0, 0, 1]
  set E' : Matrix (Fin 3) (Fin 3) k := !![1, d 1 / c, d 2 / c; 0, 1, 0; 0, 0, 1]
  have hEE' : E * E' = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, E', Matrix.mul_apply, Fin.sum_univ_three]
  have hE'E : E' * E = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, E', Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨γ * E, E' * γ', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE', Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ', h2, Matrix.one_mul, hE'E]
  · intro i
    simp [E, Matrix.mul_apply, Fin.sum_univ_three, hc i]
  · intro j hj
    have hexp : ∀ j', u ⬝ᵥ (fun i => (γ * E) i j') = ∑ l, d l * E l j' := by
      intro j'
      simp only [dotProduct, Matrix.mul_apply, hdd, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hexp]
    fin_cases j
    · exact absurd rfl hj
    · simp [E, Fin.sum_univ_three]; field_simp; ring
    · simp [E, Fin.sum_univ_three]; field_simp; ring

theorem exists_alpha (v u : Fin 3 → k) (hv : v ≠ 0) (hu : u ≠ 0) (h : u ⬝ᵥ v = 0) :
    ∃ α α' : Matrix (Fin 3) (Fin 3) k, α * α' = 1 ∧ α' * α = 1 ∧ (∀ i, α i 0 = v i) ∧
      u ⬝ᵥ (fun i => α i 1) = 0 := by
  obtain ⟨γ, γ', h1, h2, hc⟩ := exists_extend v hv
  set d : Fin 3 → k := fun j => u ⬝ᵥ (fun i => γ i j) with hdd
  have hexp : ∀ E : Matrix (Fin 3) (Fin 3) k, ∀ j', u ⬝ᵥ (fun i => (γ * E) i j') = ∑ l, d l * E l j' := by
    intro E j'
    simp only [dotProduct, Matrix.mul_apply, hdd, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmk : ∀ E E' : Matrix (Fin 3) (Fin 3) k, E * E' = 1 → E' * E = 1 → (∀ i, E i 0 = if i = 0 then 1 else 0) →
      ∑ l, d l * E l 1 = 0 → ∃ α α' : Matrix (Fin 3) (Fin 3) k, α * α' = 1 ∧ α' * α = 1 ∧
        (∀ i, α i 0 = v i) ∧ u ⬝ᵥ (fun i => α i 1) = 0 := by
    intro E E' hEE' hE'E hE0 hsum
    refine ⟨γ * E, E' * γ', ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE', Matrix.one_mul, h1]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ', h2, Matrix.one_mul, hE'E]
    · intro i
      simp [Matrix.mul_apply, Fin.sum_univ_three, hE0, hc i]
    · rw [hexp]; exact hsum
  by_cases h2' : d 2 = 0
  · refine hmk !![1, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 0, 1, 0] ?_ ?_ ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp
    · simp [Fin.sum_univ_three, h2']
  · refine hmk !![1, 0, 0; 0, 1, 0; 0, -(d 1 / d 2), 1] !![1, 0, 0; 0, 1, 0; 0, d 1 / d 2, 1]
      ?_ ?_ ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp
    · simp [Fin.sum_univ_three]; field_simp; ring

end bases

section order

open Configuration Configuration.ProjectivePlane

theorem order_ofField (l : ℕ) [Fact l.Prime] [Fintype (ℙ (ZMod l) (Fin 3 → ZMod l))] :
    order (ℙ (ZMod l) (Fin 3 → ZMod l)) (ℙ (ZMod l) (Fin 3 → ZMod l)) = l := by
  classical
  have h1 := card_points (ℙ (ZMod l) (Fin 3 → ZMod l)) (ℙ (ZMod l) (Fin 3 → ZMod l))
  have h2 : Nat.card (ℙ (ZMod l) (Fin 3 → ZMod l)) = ∑ i ∈ Finset.range 3, Nat.card (ZMod l) ^ i :=
    Projectivization.card_of_finrank (ZMod l) (Fin 3 → ZMod l) (by simp)
  rw [Nat.card_eq_fintype_card, h1, Nat.card_zmod] at h2
  simp [Finset.sum_range_succ] at h2
  set q := order (ℙ (ZMod l) (Fin 3 → ZMod l)) (ℙ (ZMod l) (Fin 3 → ZMod l))
  rcases lt_trichotomy q l with hlt | heq | hgt
  · have : q ^ 2 + q < l ^ 2 + l := by nlinarith
    omega
  · exact heq
  · have : l ^ 2 + l < q ^ 2 + q := by nlinarith
    omega

end order

end RankRings

namespace RankRings

section lift

theorem exists_lift (l : ℕ) [Fact l.Prime] (β β' : Matrix (Fin 3) (Fin 3) (ZMod l))
    (h : β * β' = 1) :
    ∃ B B' : Matrix (Fin 3) (Fin 3) ℤ_[l], B * B' = 1 ∧ B' * B = 1 ∧
      B.map PadicInt.toZMod = β ∧ B'.map PadicInt.toZMod = β' := by
  classical
  have hsurj : Function.Surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l) :=
    ZMod.ringHom_surjective _
  let B : Matrix (Fin 3) (Fin 3) ℤ_[l] := fun i j => Function.surjInv hsurj (β i j)
  have hB : B.map PadicInt.toZMod = β := by
    ext i j; exact Function.surjInv_eq hsurj (β i j)
  have hdet : PadicInt.toZMod B.det = β.det := by
    rw [RingHom.map_det]; congr 1
  have hβ : IsUnit β.det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hunit : IsUnit B.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, hdet]
    exact hβ.ne_zero
  refine ⟨B, B⁻¹, Matrix.mul_nonsing_inv B hunit, Matrix.nonsing_inv_mul B hunit, hB, ?_⟩
  have h1 : β * (B⁻¹).map PadicInt.toZMod = 1 := by
    rw [← hB, ← Matrix.map_mul, Matrix.mul_nonsing_inv B hunit]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : β' * β = 1 := mul_eq_one_comm.mp h
  calc (B⁻¹).map PadicInt.toZMod = (β' * β) * (B⁻¹).map PadicInt.toZMod := by rw [h2, Matrix.one_mul]
    _ = β' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end lift

end RankRings

end

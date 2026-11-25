import RankRings.Words
import RankRings.WordsBlock
import RankRings.Geom

/-! Part B assembled: the `l`-adic approximate solutions of the relations
of `B_l` on words, over `ℤ_[l]`. Mathlib only. -/

open Finset Matrix
open scoped LinearAlgebra.Projectivization

namespace RankRings

section exotic

variable {l : ℕ} [Fact l.Prime]

local notation "Pt" => ℙ (ZMod l) (Fin 3 → ZMod l)

theorem mem_iff_dot (p L : Pt) : p ∈ L ↔ p.rep ⬝ᵥ L.rep = 0 := by
  rw [Configuration.ofField.mem_iff]
  conv_lhs => rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep L]
  exact Projectivization.orthogonal_mk _ _

theorem dvd_of_toZMod_eq_zero {x : ℤ_[l]} (hx : PadicInt.toZMod x = 0) : (l : ℤ_[l]) ∣ x := by
  have : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hx
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact this

/-- data at a point: an invertible matrix over `ℤ_[l]` whose reduction has first column `p`
and other two columns on the line `σ p` -/
theorem exists_B (σ : Pt ≃ Pt) (hσ : ∀ p, p ∉ σ p) (p : Pt) :
    ∃ B B' : Matrix (Fin 3) (Fin 3) ℤ_[l], B * B' = 1 ∧ B' * B = 1 ∧
      (∀ i, (B.map PadicInt.toZMod) i 0 = p.rep i) ∧
      (∀ j, j ≠ 0 → (σ p).rep ⬝ᵥ (fun i => (B.map PadicInt.toZMod) i j) = 0) := by
  have h : (σ p).rep ⬝ᵥ p.rep ≠ 0 := by
    intro h0; apply hσ p; rw [mem_iff_dot, dotProduct_comm]; exact h0
  obtain ⟨β, β', h1, _, hc, hz⟩ := exists_beta p.rep (σ p).rep h
  obtain ⟨B, B', hB1, hB2, hBm, _⟩ := exists_lift l β β' h1
  exact ⟨B, B', hB1, hB2, by rw [hBm]; exact hc, by rw [hBm]; exact hz⟩

/-- data at an incident pair -/
theorem exists_A (σ : Pt ≃ Pt) (p p' : Pt) :
    ∃ A A' : Matrix (Fin 3) (Fin 3) ℤ_[l], A * A' = 1 ∧ A' * A = 1 ∧
      (p ∈ σ p' → (∀ i, (A.map PadicInt.toZMod) i 0 = p.rep i) ∧
        (σ p').rep ⬝ᵥ (fun i => (A.map PadicInt.toZMod) i 1) = 0) := by
  by_cases hp : p ∈ σ p'
  · have h : (σ p').rep ⬝ᵥ p.rep = 0 := by rw [dotProduct_comm, ← mem_iff_dot]; exact hp
    obtain ⟨α, α', h1, _, hc, hz⟩ :=
      exists_alpha p.rep (σ p').rep p.rep_nonzero (σ p').rep_nonzero h
    obtain ⟨A, A', hA1, hA2, hAm, _⟩ := exists_lift l α α' h1
    exact ⟨A, A', hA1, hA2, fun _ => ⟨by rw [hAm]; exact hc, by rw [hAm]; exact hz⟩⟩
  · exact ⟨1, 1, by simp, by simp, fun h => absurd h hp⟩

/-- the column `0` of `B'_p A_{pp'}` is `e_0` modulo `l` -/
theorem col0 {B B' A : Matrix (Fin 3) (Fin 3) ℤ_[l]} (hBB : B' * B = 1)
    (hcol : ∀ i, (A.map PadicInt.toZMod) i 0 = (B.map PadicInt.toZMod) i 0) (i : Fin 3) (hi : i ≠ 0) :
    (l : ℤ_[l]) ∣ (B' * A) i 0 := by
  apply dvd_of_toZMod_eq_zero
  have h1 : (B'.map PadicInt.toZMod * B.map PadicInt.toZMod) = 1 := by
    rw [← Matrix.map_mul, hBB]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have : PadicInt.toZMod ((B' * A) i 0) = (B'.map PadicInt.toZMod * A.map PadicInt.toZMod) i 0 := by
    rw [← Matrix.map_mul]; rfl
  rw [this, Matrix.mul_apply]
  simp only [hcol]
  rw [← Matrix.mul_apply, h1, Matrix.one_apply_ne hi]

/-- the row `0` of `B'_{p'} A` vanishes modulo `l` on columns whose reduction lies on the line -/
theorem row0 {B B' A : Matrix (Fin 3) (Fin 3) ℤ_[l]} (hBB : B * B' = 1) (u v : Fin 3 → ZMod l)
    (hcol0 : ∀ i, (B.map PadicInt.toZMod) i 0 = v i) (huv : u ⬝ᵥ v ≠ 0)
    (hz : ∀ j, j ≠ 0 → u ⬝ᵥ (fun i => (B.map PadicInt.toZMod) i j) = 0)
    (j : Fin 3) (hj : u ⬝ᵥ (fun i => (A.map PadicInt.toZMod) i j) = 0) :
    (l : ℤ_[l]) ∣ (B' * A) 0 j := by
  apply dvd_of_toZMod_eq_zero
  set β := B.map PadicInt.toZMod
  set β' := B'.map PadicInt.toZMod
  set y : Fin 3 → ZMod l := fun i => (A.map PadicInt.toZMod) i j
  have h1 : β * β' = 1 := by
    rw [← Matrix.map_mul, hBB]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hy : y = β *ᵥ (β' *ᵥ y) := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hdot : u ⬝ᵥ y = ∑ i, (u ᵥ* β) i * (β' *ᵥ y) i := by
    conv_lhs => rw [hy]
    rw [Matrix.dotProduct_mulVec]; rfl
  have hv0 : (u ᵥ* β) 0 = u ⬝ᵥ v := by
    simp only [Matrix.vecMul, dotProduct]
    congr 1; funext i; rw [hcol0 i]
  have hvj : ∀ j', j' ≠ 0 → (u ᵥ* β) j' = 0 := by
    intro j' hj'
    have := hz j' hj'
    simpa [Matrix.vecMul, dotProduct] using this
  rw [Fin.sum_univ_three, hvj 1 (by decide), hvj 2 (by decide), hv0] at hdot
  have hzero : (β' *ᵥ y) 0 = 0 := by
    have : u ⬝ᵥ v * (β' *ᵥ y) 0 = 0 := by rw [← hj]; simp [hdot]
    exact (mul_eq_zero.mp this).resolve_left huv
  have : PadicInt.toZMod ((B' * A) 0 j) = (β' *ᵥ y) 0 := by
    simp only [β', y, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]
  rw [this, hzero]

theorem dg_compl {m : ℕ} (X : Finset (Word m)) :
    (1 : Matrix (Word m) (Word m) ℤ_[l]) - dg X = dg Xᶜ := by
  ext w w'
  by_cases h : w = w'
  · subst h; by_cases hw : w ∈ X <;> simp [dg, hw]
  · simp [dg, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

theorem dg_mul_dg {m : ℕ} (X : Finset (Word m)) :
    (dg X : Matrix (Word m) (Word m) ℤ_[l]) * dg X = dg X := by
  simp only [dg, Matrix.diagonal_mul_diagonal]
  congr 1; funext w; by_cases hw : w ∈ X <;> simp [hw]

theorem dg_T_mul_M {m k : ℕ} (i : Fin 3) :
    (dg (T m k) : Matrix (Word m) (Word m) ℤ_[l]) * M ℤ_[l] m k i = M ℤ_[l] m k i := by
  ext v w
  simp only [dg, Matrix.diagonal_mul, M, Matrix.of_apply]
  by_cases hv : v ∈ T m k <;> simp [hv]

end exotic


section main

open Configuration

theorem compl_zero : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
theorem compl_zero_one : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide

theorem exotic (l : ℕ) [Fact l.Prime]
    (σ : ℙ (ZMod l) (Fin 3 → ZMod l) ≃ ℙ (ZMod l) (Fin 3 → ZMod l)) (hσ : ∀ p, p ∉ σ p) :
    ∃ (F : ℙ (ZMod l) (Fin 3 → ZMod l) → ∀ k : ℕ, Matrix (Word (3*k+1)) (Word (3*k+1)) ℤ_[l])
      (G : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) →
        ∀ k : ℕ, Matrix (Word (3*k+1)) (Word (3*k+1)) ℤ_[l])
      (X Y : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) → Fin 3 →
        ∀ k : ℕ, Matrix (Word (3*k+1)) (Word (3*k+1)) ℤ_[l]),
      (∀ p k, F p k * F p k = F p k) ∧
      (∀ p p', p ∈ σ p' → ∀ k, ∑ i, Y p p' i k * G p p' k * X p p' i k = 1) ∧
      (∀ p p', p ∈ σ p' → ∀ t : ℕ, ∀ δ : ℝ, 0 < δ → ∃ K0 : ℕ, ∀ k ≥ K0,
        (∃ Q Rm Z : Matrix (Word (3*k+1)) (Word (3*k+1)) ℤ_[l], ∃ W : Finset (Word (3*k+1)),
          (1 - F p k) * G p p' k = (l : ℤ_[l]) ^ t • Q + Rm * dg W * Z ∧
            (W.card : ℝ) ≤ δ * 3 ^ (3*k+1)) ∧
        (∃ Q Rm Z : Matrix (Word (3*k+1)) (Word (3*k+1)) ℤ_[l], ∃ W : Finset (Word (3*k+1)),
          F p' k * G p p' k = (l : ℤ_[l]) ^ t • Q + Rm * dg W * Z ∧
            (W.card : ℝ) ≤ δ * 3 ^ (3*k+1))) := by
  classical
  choose B B' hB1 hB2 hBc hBz using exists_B σ hσ
  choose A A' hA1 hA2 hAp using exists_A σ
  let D0 : ∀ k : ℕ, Finset (Word (3*k+1)) := fun k => univ.filter fun w => k + 1 ≤ cnt {0} w
  have tinv : ∀ (m : ℕ) (C C' : Matrix (Fin 3) (Fin 3) ℤ_[l]), C * C' = 1 →
      tpow m C * tpow m C' = 1 := by
    intro m C C' h; rw [← tpow_mul, h, tpow_one]
  refine ⟨fun p k => tpow _ (B p) * dg (D0 k) * tpow _ (B' p),
    fun p p' k => tpow _ (A p p') * dg (T _ k) * tpow _ (A' p p'),
    fun p p' i k => tpow _ (A p p') * M ℤ_[l] _ k i,
    fun p p' i k => (M ℤ_[l] _ k i).transpose * tpow _ (A' p p'), ?_, ?_, ?_⟩
  · -- idempotent
    intro p k
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (tpow _ (B' p)) (tpow _ (B p)), tinv _ _ _ (hB2 p), Matrix.one_mul,
      ← Matrix.mul_assoc (dg (D0 k)) (dg (D0 k)), dg_mul_dg]
  · -- the sum
    intro p p' _ k
    have h1 : ∀ i, (M ℤ_[l] (3*k+1) k i).transpose * tpow _ (A' p p') *
        (tpow _ (A p p') * dg (T _ k) * tpow _ (A' p p')) * (tpow _ (A p p') * M ℤ_[l] _ k i)
        = (M ℤ_[l] (3*k+1) k i).transpose * M ℤ_[l] _ k i := by
      intro i
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (tpow _ (A' p p')) (tpow _ (A p p')), tinv _ _ _ (hA2 p p'),
        Matrix.one_mul, ← Matrix.mul_assoc (tpow _ (A' p p')) (tpow _ (A p p')),
        tinv _ _ _ (hA2 p p'), Matrix.one_mul, dg_T_mul_M]
    simp only [h1]
    exact sum_transpose_M_mul_M ℤ_[l] rfl
  · intro p p' hp t δ hδ
    obtain ⟨K, hK⟩ := window_le t δ hδ
    refine ⟨K, fun k hk => ⟨?_, ?_⟩⟩
    · -- (1 - f_p) g
      set m := 3 * k + 1
      have hdiv : ∀ i j, j ∈ ({0} : Finset (Fin 3)) → i ∉ ({0} : Finset (Fin 3)) →
          (l : ℤ_[l]) ∣ (B' p * A p p') i j := by
        intro i j hj hi
        rw [Finset.mem_singleton] at hj hi
        subst hj
        refine col0 (hB2 p) (fun i' => ?_) i hi
        rw [(hAp p p' hp).1 i', hBc p i']
      have hX : ∀ w ∈ (D0 k)ᶜ, cnt {0} w < k + 1 := by
        intro w hw; simpa [D0] using hw
      have hY : ∀ w ∈ T m k, k + 1 ≤ cnt {0} w := by
        intro w hw; rw [cnt_singleton]; exact (mem_T.mp hw).1
      obtain ⟨Q, Rm, hQ⟩ := offblock {0} {0} (B' p * A p p') (l : ℤ_[l]) hdiv (k + 1) t
        ((D0 k)ᶜ) (T m k) hX hY
      refine ⟨(l : ℤ_[l]) • (tpow m (B p) * Q * tpow m (A' p p')), tpow m (B p) * Rm,
        tpow m (A' p p'), (T m k).filter fun w => cnt {0} w < k + 1 + t, ?_, ?_⟩
      · have hF : (1 : Matrix (Word m) (Word m) ℤ_[l]) - tpow m (B p) * dg (D0 k) * tpow m (B' p)
            = tpow m (B p) * dg (D0 k)ᶜ * tpow m (B' p) := by
          rw [← dg_compl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tinv _ _ _ (hB1 p)]
        rw [hF]
        have : tpow m (B p) * dg (D0 k)ᶜ * tpow m (B' p) *
            (tpow m (A p p') * dg (T m k) * tpow m (A' p p'))
            = tpow m (B p) * (dg (D0 k)ᶜ * tpow m (B' p * A p p') * dg (T m k)) *
              tpow m (A' p p') := by
          rw [tpow_mul]; simp only [Matrix.mul_assoc]
        rw [this, hQ, pow_succ, mul_smul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc]
      · have hsub : ((T m k).filter fun w => cnt {0} w < k + 1 + t) ⊆
            (univ.filter fun w : Word (3 * k + 1) => k ≤ cnt1 0 w + t ∧ cnt1 0 w ≤ k + t) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          rw [cnt_singleton] at hw
          have := (mem_T.mp hw.1).1
          omega
        calc ((((T m k).filter fun w => cnt {0} w < k + 1 + t).card : ℕ) : ℝ)
            ≤ ((univ.filter fun w : Word (3 * k + 1) => k ≤ cnt1 0 w + t ∧ cnt1 0 w ≤ k + t).card
                : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ δ * 3 ^ (3 * k + 1) := hK k hk 0
    · -- f_p' g
      set m := 3 * k + 1
      have huv : (σ p').rep ⬝ᵥ p'.rep ≠ 0 := by
        intro h0; apply hσ p'; rw [mem_iff_dot, dotProduct_comm]; exact h0
      have hdiv : ∀ i j, j ∈ ({0, 1} : Finset (Fin 3)) → i ∉ ({1, 2} : Finset (Fin 3)) →
          (l : ℤ_[l]) ∣ (B' p' * A p p') i j := by
        intro i j hj hi
        have hi0 : i = 0 := by fin_cases i <;> simp_all
        subst hi0
        refine row0 (hB1 p') (σ p').rep p'.rep (hBc p') huv (hBz p') j ?_
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst hj
          have : (fun i => ((A p p').map PadicInt.toZMod) i 0) = p.rep := by
            funext i; exact (hAp p p' hp).1 i
          rw [this, dotProduct_comm, ← mem_iff_dot]; exact hp
        · rw [Finset.mem_singleton] at hj; subst hj
          exact (hAp p p' hp).2
      have hX : ∀ w ∈ D0 k, cnt {1, 2} w < 2 * k + 1 := by
        intro w hw
        have h1 : k + 1 ≤ cnt {0} w := by simpa [D0] using hw
        have h2 := cnt_compl {0} w
        rw [compl_zero] at h2
        omega
      have hY : ∀ w ∈ T m k, 2 * k + 1 ≤ cnt {0, 1} w := by
        intro w hw
        have h1 := (mem_T.mp hw).2
        have h2 := cnt_compl {0, 1} w
        rw [compl_zero_one, cnt_singleton] at h2
        omega
      obtain ⟨Q, Rm, hQ⟩ := offblock {0, 1} {1, 2} (B' p' * A p p') (l : ℤ_[l]) hdiv
        (2 * k + 1) t (D0 k) (T m k) hX hY
      refine ⟨(l : ℤ_[l]) • (tpow m (B p') * Q * tpow m (A' p p')), tpow m (B p') * Rm,
        tpow m (A' p p'), (T m k).filter fun w => cnt {0, 1} w < 2 * k + 1 + t, ?_, ?_⟩
      · have : tpow m (B p') * dg (D0 k) * tpow m (B' p') *
            (tpow m (A p p') * dg (T m k) * tpow m (A' p p'))
            = tpow m (B p') * (dg (D0 k) * tpow m (B' p' * A p p') * dg (T m k)) *
              tpow m (A' p p') := by
          rw [tpow_mul]; simp only [Matrix.mul_assoc]
        rw [this, hQ, pow_succ, mul_smul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc]
      · have hsub : ((T m k).filter fun w => cnt {0, 1} w < 2 * k + 1 + t) ⊆
            (univ.filter fun w : Word (3 * k + 1) => k ≤ cnt1 2 w + t ∧ cnt1 2 w ≤ k + t) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          have h1 := (mem_T.mp hw.1).2
          have h2 := cnt_compl {0, 1} w
          rw [compl_zero_one, cnt_singleton] at h2
          omega
        calc ((((T m k).filter fun w => cnt {0, 1} w < 2 * k + 1 + t).card : ℕ) : ℝ)
            ≤ ((univ.filter fun w : Word (3 * k + 1) => k ≤ cnt1 2 w + t ∧ cnt1 2 w ≤ k + t).card
                : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ δ * 3 ^ (3 * k + 1) := hK k hk 2

end main

end RankRings

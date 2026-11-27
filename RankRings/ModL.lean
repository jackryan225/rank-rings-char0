module

public import RankRings.FiniteForm

@[expose] public section
/-!
# Cor 2(iii): exact finite-dimensional representations over `𝔽_ℓ`

The construction of `exotic`, made directly over the field `ZMod l` (the reductions modulo `ℓ` of the
`ℓ`-adic matrices of `exotic`), satisfies all relations of `B_ℓ` exactly: over a field the off-block
entries vanish, so the off-diagonal blocks of the tensor powers are `0` (`dvd_tpow` with divisor `0`).
-/

open Finset Matrix Filter
open scoped LinearAlgebra.Projectivization

namespace RankRings

section ring

variable {R : Type*} [CommRing R] {m : ℕ}

theorem dg_mul_dg' (X : Finset (Word m)) :
    (dg X : Matrix (Word m) (Word m) R) * dg X = dg X := by
  simp only [dg, Matrix.diagonal_mul_diagonal]
  congr 1; funext w; by_cases hw : w ∈ X <;> simp [hw]

theorem dg_compl' (X : Finset (Word m)) :
    (1 : Matrix (Word m) (Word m) R) - dg X = dg Xᶜ := by
  ext w w'
  by_cases h : w = w'
  · subst h; by_cases hw : w ∈ X <;> simp [dg, hw]
  · simp [dg, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

theorem dg_T_mul_M' {k : ℕ} (i : Fin 3) :
    (dg (T m k) : Matrix (Word m) (Word m) R) * M R m k i = M R m k i := by
  ext v w
  simp only [dg, Matrix.diagonal_mul, M, Matrix.of_apply]
  by_cases hv : v ∈ T m k <;> simp [hv]

/-- The off-diagonal block of a tensor power vanishes when the off-block entries of `C` vanish. -/
theorem offblock_zero (I J : Finset (Fin 3)) (C : Matrix (Fin 3) (Fin 3) R)
    (h : ∀ i j, j ∈ I → i ∉ J → C i j = 0) (k : ℕ) (X Y : Finset (Word m))
    (hX : ∀ w ∈ X, cnt J w < k) (hY : ∀ w ∈ Y, k ≤ cnt I w) :
    dg X * tpow m C * dg Y = (0 : Matrix (Word m) (Word m) R) := by
  ext w w'
  simp only [dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hw : w ∈ X
  · by_cases hw' : w' ∈ Y
    · simp only [hw, hw', ite_true, one_mul, mul_one]
      have := dvd_tpow I J C (0 : R) (fun i j hj hi => zero_dvd_iff.mpr (h i j hj hi)) w w' k 0
        (by rw [Nat.add_zero]; exact hY w' hw') (hX w hw)
      rwa [zero_add, pow_one, zero_dvd_iff] at this
    · simp [hw']
  · simp [hw]

end ring

section field

variable {K : Type*} [Field K]

/-- column `0` of `β' α` is `e_0` when `α` and `β` have the same column `0` -/
theorem col0F {β β' α : Matrix (Fin 3) (Fin 3) K} (h : β' * β = 1) (hcol : ∀ i, α i 0 = β i 0)
    (i : Fin 3) (hi : i ≠ 0) : (β' * α) i 0 = 0 := by
  rw [Matrix.mul_apply]
  simp only [hcol]
  rw [← Matrix.mul_apply, h, Matrix.one_apply_ne hi]

/-- row `0` of `β' α` vanishes on the columns of `α` that lie on the line `u` -/
theorem row0F {β β' α : Matrix (Fin 3) (Fin 3) K} (h : β * β' = 1) (u v : Fin 3 → K)
    (hcol0 : ∀ i, β i 0 = v i) (huv : u ⬝ᵥ v ≠ 0)
    (hz : ∀ j, j ≠ 0 → u ⬝ᵥ (fun i => β i j) = 0)
    (j : Fin 3) (hj : u ⬝ᵥ (fun i => α i j) = 0) : (β' * α) 0 j = 0 := by
  have hy : (fun i => α i j) = β *ᵥ (β' *ᵥ (fun i => α i j)) := by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have hdot : u ⬝ᵥ (fun i => α i j) = ∑ i, (u ᵥ* β) i * (β' *ᵥ (fun i => α i j)) i := by
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
  have hzero : (β' *ᵥ (fun i => α i j)) 0 = 0 := by
    have : u ⬝ᵥ v * (β' *ᵥ (fun i => α i j)) 0 = 0 := by linear_combination hj - hdot
    exact (mul_eq_zero.mp this).resolve_left huv
  rw [← hzero]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end field

section modL

/-- **Cor 2(iii)**, matrix form, for every prime `l`: the matrices of `exotic` built over `𝔽_l`
satisfy the relations of `B_l` exactly, in dimension `3 ^ (3k+1)`, for every `k`. -/
theorem exists_config_modL (l : ℕ) [Fact l.Prime]
    (σ : ℙ (ZMod l) (Fin 3 → ZMod l) ≃ ℙ (ZMod l) (Fin 3 → ZMod l)) (hσ : ∀ p, p ∉ σ p)
    (k : ℕ) :
    ∃ (F : ℙ (ZMod l) (Fin 3 → ZMod l) → Matrix (Word (3*k+1)) (Word (3*k+1)) (ZMod l))
      (G : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) →
        Matrix (Word (3*k+1)) (Word (3*k+1)) (ZMod l))
      (X Y : ℙ (ZMod l) (Fin 3 → ZMod l) → ℙ (ZMod l) (Fin 3 → ZMod l) → Fin 3 →
        Matrix (Word (3*k+1)) (Word (3*k+1)) (ZMod l)),
      (∀ p, F p * F p = F p) ∧
      (∀ p p', p ∈ σ p' → F p * G p p' = G p p') ∧
      (∀ p p', p ∈ σ p' → F p' * G p p' = 0) ∧
      (∀ p p', p ∈ σ p' → ∑ i, Y p p' i * G p p' * X p p' i = 1) := by
  classical
  have hB : ∀ p : ℙ (ZMod l) (Fin 3 → ZMod l), ∃ β β' : Matrix (Fin 3) (Fin 3) (ZMod l),
      β * β' = 1 ∧ β' * β = 1 ∧ (∀ i, β i 0 = p.rep i) ∧
      (∀ j, j ≠ 0 → (σ p).rep ⬝ᵥ (fun i => β i j) = 0) := by
    intro p
    refine exists_beta p.rep (σ p).rep ?_
    intro h0; apply hσ p; rw [mem_iff_dot, dotProduct_comm]; exact h0
  have hA : ∀ p p' : ℙ (ZMod l) (Fin 3 → ZMod l), ∃ α α' : Matrix (Fin 3) (Fin 3) (ZMod l),
      α * α' = 1 ∧ α' * α = 1 ∧
      (p ∈ σ p' → (∀ i, α i 0 = p.rep i) ∧ (σ p').rep ⬝ᵥ (fun i => α i 1) = 0) := by
    intro p p'
    by_cases hp : p ∈ σ p'
    · have h : (σ p').rep ⬝ᵥ p.rep = 0 := by rw [dotProduct_comm, ← mem_iff_dot]; exact hp
      obtain ⟨α, α', h1, h2, hc, hz⟩ :=
        exists_alpha p.rep (σ p').rep p.rep_nonzero (σ p').rep_nonzero h
      exact ⟨α, α', h1, h2, fun _ => ⟨hc, hz⟩⟩
    · exact ⟨1, 1, by simp, by simp, fun h => absurd h hp⟩
  choose B B' hB1 hB2 hBc hBz using hB
  choose A A' hA1 hA2 hAp using hA
  set m := 3 * k + 1 with hm
  let D0 : Finset (Word m) := univ.filter fun w => k + 1 ≤ cnt {0} w
  have tinv : ∀ (C C' : Matrix (Fin 3) (Fin 3) (ZMod l)), C * C' = 1 →
      tpow m C * tpow m C' = 1 := by
    intro C C' h; rw [← tpow_mul, h, tpow_one]
  refine ⟨fun p => tpow m (B p) * dg D0 * tpow m (B' p),
    fun p p' => tpow m (A p p') * dg (T m k) * tpow m (A' p p'),
    fun p p' i => tpow m (A p p') * M (ZMod l) m k i,
    fun p p' i => (M (ZMod l) m k i).transpose * tpow m (A' p p'), ?_, ?_, ?_, ?_⟩
  · -- idempotent
    intro p
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (tpow m (B' p)) (tpow m (B p)), tinv _ _ (hB2 p), Matrix.one_mul,
      ← Matrix.mul_assoc (dg D0) (dg D0), dg_mul_dg']
  · -- f_p g = g
    intro p p' hp
    have hC : ∀ i j, j ∈ ({0} : Finset (Fin 3)) → i ∉ ({0} : Finset (Fin 3)) →
        (B' p * A p p') i j = 0 := by
      intro i j hj hi
      rw [Finset.mem_singleton] at hj hi
      subst hj
      exact col0F (hB2 p) (fun i' => by rw [(hAp p p' hp).1 i', hBc p i']) i hi
    have hX : ∀ w ∈ D0ᶜ, cnt {0} w < k + 1 := by
      intro w hw; simpa [D0] using hw
    have hY : ∀ w ∈ T m k, k + 1 ≤ cnt {0} w := by
      intro w hw; rw [cnt_singleton]; exact (mem_T.mp hw).1
    have h0 := offblock_zero {0} {0} (B' p * A p p') hC (k + 1) D0ᶜ (T m k) hX hY
    have hF : (1 : Matrix (Word m) (Word m) (ZMod l)) - tpow m (B p) * dg D0 * tpow m (B' p)
        = tpow m (B p) * dg D0ᶜ * tpow m (B' p) := by
      rw [← dg_compl', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tinv _ _ (hB1 p)]
    have key : (1 - tpow m (B p) * dg D0 * tpow m (B' p)) *
        (tpow m (A p p') * dg (T m k) * tpow m (A' p p')) = 0 := by
      rw [hF]
      have : tpow m (B p) * dg D0ᶜ * tpow m (B' p) *
          (tpow m (A p p') * dg (T m k) * tpow m (A' p p'))
          = tpow m (B p) * (dg D0ᶜ * tpow m (B' p * A p p') * dg (T m k)) *
            tpow m (A' p p') := by
        rw [tpow_mul]; simp only [Matrix.mul_assoc]
      rw [this, h0, Matrix.mul_zero, Matrix.zero_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at key
    exact key.symm
  · -- f_p' g = 0
    intro p p' hp
    have huv : (σ p').rep ⬝ᵥ p'.rep ≠ 0 := by
      intro h0; apply hσ p'; rw [mem_iff_dot, dotProduct_comm]; exact h0
    have hC : ∀ i j, j ∈ ({0, 1} : Finset (Fin 3)) → i ∉ ({1, 2} : Finset (Fin 3)) →
        (B' p' * A p p') i j = 0 := by
      intro i j hj hi
      have hi0 : i = 0 := by fin_cases i <;> simp_all
      subst hi0
      refine row0F (hB1 p') (σ p').rep p'.rep (hBc p') huv (hBz p') j ?_
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst hj
        have : (fun i => A p p' i 0) = p.rep := by funext i; exact (hAp p p' hp).1 i
        rw [this, dotProduct_comm, ← mem_iff_dot]; exact hp
      · rw [Finset.mem_singleton] at hj; subst hj
        exact (hAp p p' hp).2
    have hX : ∀ w ∈ D0, cnt {1, 2} w < 2 * k + 1 := by
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
    have h0 := offblock_zero {0, 1} {1, 2} (B' p' * A p p') hC (2 * k + 1) D0 (T m k) hX hY
    have : tpow m (B p') * dg D0 * tpow m (B' p') *
        (tpow m (A p p') * dg (T m k) * tpow m (A' p p'))
        = tpow m (B p') * (dg D0 * tpow m (B' p' * A p p') * dg (T m k)) *
          tpow m (A' p p') := by
      rw [tpow_mul]; simp only [Matrix.mul_assoc]
    rw [this, h0, Matrix.mul_zero, Matrix.zero_mul]
  · -- the sum
    intro p p' _
    have h1 : ∀ i, (M (ZMod l) m k i).transpose * tpow m (A' p p') *
        (tpow m (A p p') * dg (T m k) * tpow m (A' p p')) * (tpow m (A p p') * M (ZMod l) m k i)
        = (M (ZMod l) m k i).transpose * M (ZMod l) m k i := by
      intro i
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (tpow m (A' p p')) (tpow m (A p p')), tinv _ _ (hA2 p p'),
        Matrix.one_mul, ← Matrix.mul_assoc (tpow m (A' p p')) (tpow m (A p p')),
        tinv _ _ (hA2 p p'), Matrix.one_mul, dg_T_mul_M']
    simp only [h1]
    exact sum_transpose_M_mul_M (ZMod l) hm

/-- **Cor 2(iii)** for `ℓ = 7`, as a configuration: for every `σ` without fixed incidences and every
`k`, the relations `Config` hold exactly in `M_{3^(3k+1)}(𝔽_7)`. -/
theorem config_modL (σ : Pt ≃ Pt) (hσ : ∀ p, p ∉ σ p) (k : ℕ) :
    Nonempty (Config (Matrix (Word (3*k+1)) (Word (3*k+1)) (ZMod 7)) σ) := by
  obtain ⟨F, G, X, Y, h1, h2, h3, h4⟩ := exists_config_modL 7 σ hσ k
  exact ⟨⟨F, G, X, Y, h1, h2, h3, h4⟩⟩

/-- **Cor 2(iii)** for `ℓ = 7`, relation form: the integer relations `rel σ` of `finite_form` have
exact solutions in `N × N` matrices over `𝔽_7`, `N = 3 ^ (3k+1)`, for every `k`. -/
theorem rel_modL (σ : Pt ≃ Pt) (hσ : ∀ p, p ∉ σ p) (k : ℕ) :
    ∃ A : Gens → Matrix (Fin (3 ^ (3*k+1))) (Fin (3 ^ (3*k+1))) (ZMod 7),
      ∀ j, ev A (rel σ j) = 0 := by
  obtain ⟨c⟩ := config_modL σ hσ k
  have hcard : Fintype.card (Word (3*k+1)) = 3 ^ (3*k+1) := by simp
  let e : Word (3*k+1) ≃ Fin (3 ^ (3*k+1)) := Fintype.equivFinOfCardEq hcard
  let φ := (Matrix.reindexAlgEquiv (ZMod 7) (ZMod 7) e).toRingEquiv.toRingHom
  exact ⟨(c.map φ).toGen, rel_of_config (c.map φ)⟩

/-- **Characteristic dependence** (Cor 2(ii) over `ℂ` and Cor 2(iii) together, `ℓ = 7`): for every `σ`
without fixed incidences there is `ε > 0` such that the integer relations `rel σ` have no `ε`-approximate
solution in `M_N(ℂ)` for any `N > 0`, but exact solutions in `M_N(𝔽_7)` for all `N = 3 ^ (3k+1)`. -/
theorem char_contrast (σ : Pt ≃ Pt) (hσ : ∀ p, p ∉ σ p) : ∃ ε : ℝ, 0 < ε ∧
    (∀ N : ℕ, 0 < N → ∀ A : Gens → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((ev A (rel σ j)).rank : ℝ)) ∧
    ∀ k : ℕ, ∃ A : Gens → Matrix (Fin (3 ^ (3*k+1))) (Fin (3 ^ (3*k+1))) (ZMod 7),
      ∀ j, ev A (rel σ j) = 0 := by
  suffices H : ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, 0 < N → ∀ A : Gens → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((ev A (rel σ j)).rank : ℝ) by
    obtain ⟨ε, hε, hH⟩ := H
    exact ⟨ε, hε, hH, rel_modL σ hσ⟩
  by_contra hne
  push_neg at hne
  have hk : ∀ k : ℕ, ∃ N : ℕ, 0 < N ∧ ∃ A : Gens → Matrix (Fin N) (Fin N) ℂ,
      ∀ j, ((ev A (rel σ j)).rank : ℝ) ≤ 1 / ((k : ℝ) + 1) * N :=
    fun k => hne (1 / ((k : ℝ) + 1)) (by positivity)
  choose N hN A hA using hk
  let a : Gens → RU hyp N := fun g => RingCon.mk' _ (fun k => A k g)
  apply no_config_RU hyp N hN (configOfRel (σ := σ) a fun j => ?_)
  have e := ev_map (RingCon.mk' (rnullCon hyp N)) (fun g k => A k g) (rel σ j)
  rw [show a = fun g => RingCon.mk' (rnullCon hyp N) (fun k => A k g) from rfl, ← e,
    ← map_zero (RingCon.mk' (rnullCon hyp N)), mk_eq_iff, sub_zero]
  have hev : ∀ k, (ev (fun g => fun k => A k g) (rel σ j)) k = ev (A k) (rel σ j) := by
    intro k
    exact ev_map (Pi.evalRingHom (fun k => Matrix (Fin (N k)) (Fin (N k)) ℂ) k)
      (fun g => fun k => A k g) (rel σ j)
  unfold IsRNull
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) (hyp : Filter ℕ) (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left
      (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_) (fun k => ?_)
  · positivity
  · simp only [hev]
    have hNk : (0 : ℝ) < N k := by exact_mod_cast hN k
    rw [div_le_iff₀ hNk]
    exact hA k j

/-- **Finite form with characteristic dependence**, in the shape of `finite_form`: one finite set of
integer relations, no `ε`-approximate complex matrix solution in any size, exact solutions over `𝔽_7`
in arbitrarily large sizes. -/
theorem finite_form_modL : ∃ (Gn Rl : Type) (_ : Fintype Gn) (_ : Fintype Rl)
    (rel : Rl → FreeAlgebra ℤ Gn) (ε : ℝ), 0 < ε ∧
    (∀ N : ℕ, 0 < N → ∀ A : Gn → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((FreeAlgebra.lift ℤ A (rel j)).rank : ℝ)) ∧
    ∀ k : ℕ, ∃ A : Gn → Matrix (Fin (3 ^ (3*k+1))) (Fin (3 ^ (3*k+1))) (ZMod 7),
      ∀ j, FreeAlgebra.lift ℤ A (rel j) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_sigma_Pt
  obtain ⟨ε, hε, hC, hF⟩ := char_contrast σ hσ
  refine ⟨Gens, Rl σ, inferInstance, inferInstance, rel σ, ε, hε, fun N hN A => ?_, fun k => ?_⟩
  · obtain ⟨j, hj⟩ := hC N hN A
    exact ⟨j, by rw [lift_eq_ev]; exact hj⟩
  · obtain ⟨A, hA⟩ := hF k
    exact ⟨A, fun j => by rw [lift_eq_ev]; exact hA j⟩

end modL

end RankRings

#print axioms RankRings.exists_config_modL
#print axioms RankRings.config_modL
#print axioms RankRings.rel_modL
#print axioms RankRings.char_contrast
#print axioms RankRings.finite_form_modL

end

import Mathlib

/-! Words in three letters. Mathlib only.
B1 tensor powers, B2 interleaving, B3 anticoncentration, B4 the exact third. -/

open Finset

namespace RankRings

/-- words of length `m` in three letters -/
abbrev Word (m : ℕ) := Fin m → Fin 3

/-! ### B1: tensor powers -/

section tpow
variable {R : Type*} [CommRing R] {m : ℕ}

/-- tensor power of a `3 × 3` matrix, indexed by words -/
def tpow (m : ℕ) (C : Matrix (Fin 3) (Fin 3) R) : Matrix (Word m) (Word m) R :=
  Matrix.of fun w w' => ∏ s, C (w s) (w' s)

theorem tpow_apply (C : Matrix (Fin 3) (Fin 3) R) (w w' : Word m) :
    tpow m C w w' = ∏ s, C (w s) (w' s) := rfl

theorem tpow_mul (C D : Matrix (Fin 3) (Fin 3) R) :
    tpow m (C * D) = tpow m C * tpow m D := by
  ext w w'
  simp only [tpow_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.prod_mul_distrib]

theorem tpow_one : tpow m (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext w w'
  rw [tpow_apply, Matrix.one_apply]
  by_cases h : w = w'
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/-! ### B2: interleaving, entrywise -/

/-- number of letters of `w` in `I` -/
def cnt (I : Finset (Fin 3)) (w : Word m) : ℕ := #{s | w s ∈ I}

theorem dvd_tpow (I J : Finset (Fin 3)) (C : Matrix (Fin 3) (Fin 3) R) (l : R)
    (h : ∀ i j, j ∈ I → i ∉ J → l ∣ C i j) (w w' : Word m) (k j : ℕ)
    (hw' : k + j ≤ cnt I w') (hw : cnt J w < k) : l ^ (j + 1) ∣ tpow m C w w' := by
  classical
  set A : Finset (Fin m) := {s | w' s ∈ I} with hA
  set B : Finset (Fin m) := {s | w s ∈ J} with hB
  have hcard : j + 1 ≤ #(A \ B) := by
    have h1 : #A - #B ≤ #(A \ B) := Finset.le_card_sdiff B A
    have h2 : k + j ≤ #A := hw'
    have h3 : #B < k := hw
    omega
  have h1 : l ^ #(A \ B) ∣ ∏ s ∈ A \ B, C (w s) (w' s) := by
    rw [← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun s hs => ?_
    rw [Finset.mem_sdiff] at hs
    exact h _ _ (by simpa [hA] using hs.1) (by simpa [hB] using hs.2)
  calc l ^ (j + 1) ∣ l ^ #(A \ B) := pow_dvd_pow l hcard
    _ ∣ ∏ s ∈ A \ B, C (w s) (w' s) := h1
    _ ∣ ∏ s, C (w s) (w' s) := Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

theorem prod_le_pow_aux {ι : Type*} (A : Finset ι) (f : ι → ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (h0 : ∀ i, 0 ≤ f i) (h : ∀ i ∈ A, f i ≤ q) : ∏ i ∈ A, f i ≤ q ^ #A := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact mul_le_mul (h a (Finset.mem_insert_self a A))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      (Finset.prod_nonneg fun i _ => h0 i) hq0

/-- norm version of the interleaving estimate; no ultrametric inequality is needed -/
theorem norm_tpow_le {K : Type*} [NormedField K] {C : Matrix (Fin 3) (Fin 3) K}
    (h1 : ∀ i j, ‖C i j‖ ≤ 1) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (I J : Finset (Fin 3))
    (h : ∀ i ∉ I, ∀ j ∈ J, ‖C i j‖ ≤ q) (w w' : Word m) :
    ‖tpow m C w w'‖ ≤ q ^ (cnt J w' - cnt I w) := by
  classical
  set A : Finset (Fin m) := {s | w' s ∈ J} with hA
  set B : Finset (Fin m) := {s | w s ∈ I} with hB
  have hcard : cnt J w' - cnt I w ≤ #(A \ B) := Finset.le_card_sdiff B A
  rw [tpow_apply, norm_prod, ← Finset.prod_sdiff (Finset.subset_univ (A \ B))]
  have h2 : ∏ s ∈ univ \ (A \ B), ‖C (w s) (w' s)‖ ≤ 1 := by
    have := prod_le_pow_aux (univ \ (A \ B)) (fun s => ‖C (w s) (w' s)‖) zero_le_one
      (fun _ => norm_nonneg _) (fun _ _ => h1 _ _)
    simpa using this
  have h3 : ∏ s ∈ A \ B, ‖C (w s) (w' s)‖ ≤ q ^ #(A \ B) := by
    refine prod_le_pow_aux (A \ B) (fun s => ‖C (w s) (w' s)‖) hq0 (fun _ => norm_nonneg _) ?_
    intro s hs
    rw [Finset.mem_sdiff] at hs
    exact h _ (by simpa [hB] using hs.2) _ (by simpa [hA] using hs.1)
  calc (∏ s ∈ univ \ (A \ B), ‖C (w s) (w' s)‖) * ∏ s ∈ A \ B, ‖C (w s) (w' s)‖
      ≤ 1 * q ^ #(A \ B) :=
        mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
    _ = q ^ #(A \ B) := one_mul _
    _ ≤ q ^ (cnt J w' - cnt I w) := pow_le_pow_of_le_one hq0 hq1 hcard

/-- all entries of a tensor power of an integral matrix are integral -/
theorem norm_tpow_le_one {K : Type*} [NormedField K] {C : Matrix (Fin 3) (Fin 3) K}
    (h1 : ∀ i j, ‖C i j‖ ≤ 1) (w w' : Word m) : ‖tpow m C w w'‖ ≤ 1 := by
  rw [tpow_apply, norm_prod]
  have := prod_le_pow_aux univ (fun s => ‖C (w s) (w' s)‖) zero_le_one
    (fun _ => norm_nonneg _) (fun _ _ => h1 _ _)
  simpa using this

end tpow

/-! ### B4: one third, exactly -/

section third
variable {m : ℕ}

/-- number of letters equal to `a` -/
def cnt1 (a : Fin 3) (w : Word m) : ℕ := #{s | w s = a}

theorem cnt_singleton (a : Fin 3) (w : Word m) : cnt {a} w = cnt1 a w := by
  simp [cnt, cnt1]

theorem sum_cnt1 (w : Word m) : cnt1 0 w + cnt1 1 w + cnt1 2 w = m := by
  have h : ∑ a : Fin 3, #{s | w s = a} = #(univ : Finset (Fin m)) :=
    (Finset.card_eq_sum_card_fiberwise (f := w) (t := univ) (by simp)).symm
  simpa [cnt1, Fin.sum_univ_three] using h

/-- shift all letters by `-i` -/
def shift (i : Fin 3) (w : Word m) : Word m := fun s => w s - i

theorem cnt1_shift (i a : Fin 3) (w : Word m) : cnt1 a (shift i w) = cnt1 (a + i) w := by
  unfold cnt1 shift
  congr 1
  ext s
  simp [sub_eq_iff_eq_add]

/-- the words with at least `k + 1` letters `0` and at most `k` letters `2` -/
def T (m k : ℕ) : Finset (Word m) := {w | k + 1 ≤ cnt1 0 w ∧ cnt1 2 w ≤ k}

theorem mem_T {k : ℕ} {w : Word m} : w ∈ T m k ↔ k + 1 ≤ cnt1 0 w ∧ cnt1 2 w ≤ k := by
  simp [T]

theorem existsUnique_shift_mem_T {k : ℕ} (hm : m = 3 * k + 1) (w : Word m) :
    ∃! i : Fin 3, shift i w ∈ T m k := by
  have hs := sum_cnt1 w
  have key : ∀ i : Fin 3, shift i w ∈ T m k ↔
      (k + 1 ≤ cnt1 i w ∧ cnt1 (i + 2) w ≤ k) := by
    intro i
    rw [mem_T, cnt1_shift, cnt1_shift, zero_add, add_comm 2 i]
  simp only [key]
  have e0 : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 2 = 1 := rfl
  have ex : ∃ i : Fin 3, k + 1 ≤ cnt1 i w ∧ cnt1 (i + 2) w ≤ k := by
    rcases Nat.lt_or_ge k (cnt1 0 w) with h0 | h0
    · rcases Nat.lt_or_ge k (cnt1 2 w) with h2 | h2
      · exact ⟨2, h2, by rw [e2]; omega⟩
      · exact ⟨0, h0, by rw [e0]; exact h2⟩
    · rcases Nat.lt_or_ge k (cnt1 1 w) with h1 | h1
      · exact ⟨1, h1, by rw [e1]; exact h0⟩
      · exact ⟨2, by omega, by rw [e2]; exact h1⟩
  obtain ⟨i, hi⟩ := ex
  refine ⟨i, hi, ?_⟩
  intro j hj
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

/-- the index `i` with `shift i w ∈ T` -/
noncomputable def cls {k : ℕ} (hm : m = 3 * k + 1) (w : Word m) : Fin 3 :=
  (existsUnique_shift_mem_T hm w).choose

/-- `M i` maps the basis vector of `w` to that of `shift i w` if this is in `T`, and to `0` otherwise -/
def M (R : Type*) [Zero R] [One R] (m k : ℕ) (i : Fin 3) : Matrix (Word m) (Word m) R :=
  Matrix.of fun v w => if shift i w = v ∧ v ∈ T m k then 1 else 0

theorem shift_injective (i : Fin 3) : Function.Injective (shift (m := m) i) := by
  intro w w' h
  funext s
  have := congrFun h s
  simpa [shift] using this

theorem sum_transpose_M_mul_M (R : Type*) [CommRing R] {k : ℕ} (hm : m = 3 * k + 1) :
    ∑ i : Fin 3, (M R m k i).transpose * M R m k i = 1 := by
  ext w w'
  rw [Matrix.sum_apply]
  have h1 : ∀ i : Fin 3, ((M R m k i).transpose * M R m k i) w w'
      = if shift i w ∈ T m k ∧ w = w' then 1 else 0 := by
    intro i
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (shift i w)]
    · by_cases hT : shift i w ∈ T m k
      · by_cases hw : w = w'
        · subst hw; simp [M, hT]
        · have : shift i w' ≠ shift i w := fun h => hw (shift_injective i h).symm
          simp [M, hT, hw, this]
      · simp [M, hT]
    · intro v _ hv
      simp [M, Ne.symm hv]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h1]
  obtain ⟨i, hi, huniq⟩ := existsUnique_shift_mem_T hm w
  rw [Finset.sum_eq_single i]
  · simp [hi, Matrix.one_apply]
  · intro j _ hj
    have : shift j w ∉ T m k := fun h => hj (huniq j h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end third

/-! ### the cyclic shift as a permutation of the words -/

/-- cyclic shift of the letters -/
def rot (m : ℕ) : Equiv.Perm (Word m) where
  toFun w := fun s => w s - 1
  invFun w := fun s => w s + 1
  left_inv w := by funext s; simp
  right_inv w := by funext s; simp

theorem rot_pow (m : ℕ) (i : Fin 3) (w : Word m) : ((rot m) ^ (i : ℕ)) w = shift i w := by
  fin_cases i
  · funext s; simp [shift]
  · funext s; simp [shift, rot]
  · funext s
    simp only [Fin.reduceFinMk, pow_two, Equiv.Perm.mul_apply, shift, rot, Equiv.coe_fn_mk]
    generalize w s = x
    revert x; decide

theorem rot_pow_three (m : ℕ) : (rot m) ^ 3 = 1 := by
  ext w s
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, rot,
    Equiv.coe_fn_mk]
  generalize w s = x
  revert x; decide

/-- every word is in exactly one of the three sets `rot^{-i} T` -/
theorem part {m k : ℕ} (hm : m = 3 * k + 1) (w : Word m) :
    ∑ i : Fin 3, (if ((rot m) ^ (i : ℕ)) w ∈ T m k then (1 : ℕ) else 0) = 1 := by
  simp only [rot_pow]
  obtain ⟨i, hi, huniq⟩ := existsUnique_shift_mem_T hm w
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hj
    have : shift j w ∉ T m k := fun h => hj (huniq j h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cnt_compl (I : Finset (Fin 3)) {m : ℕ} (w : Word m) : cnt I w + cnt Iᶜ w = m := by
  classical
  have h : #(univ.filter fun s => w s ∈ I) + #(univ.filter fun s => ¬ w s ∈ I)
      = #(univ : Finset (Fin m)) := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
      Finset.filter_union_filter_not_eq]
  simpa [cnt] using h

/-! ### B3: anticoncentration -/

/-- the number of words of length `m` with exactly `c` letters `a` -/
def ncount (m : ℕ) (a : Fin 3) (c : ℕ) : ℕ := #{w : Word m | cnt1 a w = c}

/-- generating function -/
theorem sum_pow_cnt (m : ℕ) (a : Fin 3) :
    ∑ w : Word m, (Polynomial.X : Polynomial ℕ) ^ cnt1 a w = (Polynomial.X + Polynomial.C 2) ^ m := by
  have h : ∀ w : Word m, (Polynomial.X : Polynomial ℕ) ^ cnt1 a w
      = ∏ s, (if w s = a then Polynomial.X else 1) := by
    intro w
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rfl
  simp only [h]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin 3)))
    (fun _ b => if b = a then (Polynomial.X : Polynomial ℕ) else 1)
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∑ b : Fin 3, (if b = a then (Polynomial.X : Polynomial ℕ) else 1)
      = Polynomial.X + Polynomial.C 2 := by
    fin_cases a <;> simp [Fin.sum_univ_three] <;> ring
  simp [h3]

theorem ncount_eq (m : ℕ) (a : Fin 3) (c : ℕ) : ncount m a c = 2 ^ (m - c) * m.choose c := by
  have h := congrArg (fun p : Polynomial ℕ => p.coeff c) (sum_pow_cnt m a)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at h
  rw [Polynomial.coeff_X_add_C_pow] at h
  rw [ncount, Finset.card_filter]
  rw [Nat.cast_id] at h
  rw [← h]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hc : cnt1 a w = c
  · simp [hc]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.symm)]

theorem sum_ncount_le (m : ℕ) (a : Fin 3) (s : Finset ℕ) : ∑ c ∈ s, ncount m a c ≤ 3 ^ m := by
  have h : ∑ c ∈ s, ncount m a c = #{w : Word m | cnt1 a w ∈ s} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cnt1 a) (t := s)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      unfold ncount
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨h ▸ hc, h⟩
      · intro h; exact h.2
    · intro w hw
      simpa using hw
  rw [h]
  calc #{w : Word m | cnt1 a w ∈ s} ≤ #(univ : Finset (Word m)) := Finset.card_filter_le _ _
    _ = 3 ^ m := by simp

/-- one step: the counts decrease slowly up to `k + B` -/
theorem ncount_succ (k B c : ℕ) (a : Fin 3) (hc : c ≤ k + B) (hB : 3 * B + 1 ≤ 2 * k) :
    (2 * k - (3 * B + 1)) * ncount (3 * k + 1) a c ≤ 2 * k * ncount (3 * k + 1) a (c + 1) := by
  set m := 3 * k + 1 with hm
  have hcm : c + 1 ≤ m := by omega
  rw [ncount_eq, ncount_eq]
  have hpow : 2 ^ (m - c) = 2 * 2 ^ (m - (c + 1)) := by
    rw [show m - c = (m - (c + 1)) + 1 by omega, pow_succ]; ring
  have hch : m.choose (c + 1) * (c + 1) = m.choose c * (m - c) := Nat.choose_succ_right_eq m c
  rw [hpow]
  -- multiply by `c + 1`
  have hpos : 0 < c + 1 := Nat.succ_pos c
  refine Nat.le_of_mul_le_mul_right (c := c + 1) ?_ hpos
  have hkey : (2 * k - (3 * B + 1)) * (2 * (c + 1)) ≤ 2 * k * (m - c) := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hc
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hB
    have e1 : 2 * k - (3 * B + 1) = u := by omega
    have e2 : m - c = 2 * k + 1 - B + t := by omega
    rw [e1, e2]
    have hB' : B ≤ 2 * k + 1 := by omega
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hB'
    have e3 : 2 * k + 1 - B = v := by omega
    rw [e3]
    have hc' : c + 1 ≤ k + B + 1 := by omega
    calc u * (2 * (c + 1)) ≤ u * (2 * (k + B + 1)) := by gcongr
      _ ≤ 2 * k * (v + t) := by
        have : u * (2 * (k + B + 1)) ≤ 2 * k * v := by
          have hku : 2 * k = 3 * B + 1 + u := hu
          have hvv : v = 2 * k + 1 - B := by omega
          have hv2 : v = 2 * B + 2 + u := by omega
          rw [hv2]
          have : 2 * (k + B + 1) = u + (5 * B + 3) := by omega
          rw [this, hku]
          nlinarith [Nat.zero_le (u * B), Nat.zero_le B, Nat.zero_le u]
        calc u * (2 * (k + B + 1)) ≤ 2 * k * v := this
          _ ≤ 2 * k * (v + t) := by gcongr; omega
  calc (2 * k - (3 * B + 1)) * (2 * 2 ^ (m - (c + 1)) * m.choose c) * (c + 1)
      = ((2 * k - (3 * B + 1)) * (2 * (c + 1))) * (2 ^ (m - (c + 1)) * m.choose c) := by ring
    _ ≤ (2 * k * (m - c)) * (2 ^ (m - (c + 1)) * m.choose c) := by gcongr
    _ = 2 * k * 2 ^ (m - (c + 1)) * (m.choose c * (m - c)) := by ring
    _ = 2 * k * 2 ^ (m - (c + 1)) * (m.choose (c + 1) * (c + 1)) := by rw [hch]
    _ = 2 * k * (2 ^ (m - (c + 1)) * m.choose (c + 1)) * (c + 1) := by ring

/-- `r` steps -/
theorem ncount_add (k B c r : ℕ) (a : Fin 3) (hc : c + r ≤ k + B + 1) (hk : 0 < k)
    (hr : r * (3 * B + 1) ≤ k) :
    ncount (3 * k + 1) a c ≤ 2 * ncount (3 * k + 1) a (c + r) := by
  -- real version with Bernoulli
  have main : ∀ r : ℕ, c + r ≤ k + B + 1 → r * (3 * B + 1) ≤ k →
      (2 * k - r * (3 * B + 1)) * ncount (3 * k + 1) a c ≤ 2 * k * ncount (3 * k + 1) a (c + r) := by
    intro r
    induction r with
    | zero => intro _ _; simp
    | succ r ih =>
      intro h1 h2
      have h2' : r * (3 * B + 1) ≤ k := le_trans (by gcongr; omega) h2
      have ih' := ih (by omega) h2'
      have hB : 3 * B + 1 ≤ 2 * k := by nlinarith
      have hs := ncount_succ k B (c + r) a (by omega) hB
      have hk2 : 0 < 2 * k := by omega
      refine Nat.le_of_mul_le_mul_left (c := 2 * k) ?_ hk2
      set N0 := ncount (3 * k + 1) a c
      set N1 := ncount (3 * k + 1) a (c + r)
      set N2 := ncount (3 * k + 1) a (c + (r + 1))
      have hs' : (2 * k - (3 * B + 1)) * N1 ≤ 2 * k * N2 := hs
      obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hB
      have hr2 : (r + 1) * (3 * B + 1) ≤ 2 * k := le_trans h2 (by omega)
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hr2
      have hr3 : r * (3 * B + 1) ≤ 2 * k := le_trans h2' (by omega)
      have e1 : 2 * k - (3 * B + 1) = p := by omega
      have e2 : 2 * k - (r + 1) * (3 * B + 1) = q := by omega
      have e3 : 2 * k - r * (3 * B + 1) = q + (3 * B + 1) := by
        have : (r + 1) * (3 * B + 1) = r * (3 * B + 1) + (3 * B + 1) := by ring
        omega
      rw [e2]
      rw [e1] at hs'
      rw [e3] at ih'
      calc 2 * k * (q * N0) ≤ p * ((q + (3 * B + 1)) * N0) := by
            have : 2 * k * q ≤ p * (q + (3 * B + 1)) := by
              have hpq : q ≤ p := by
                have : (r + 1) * (3 * B + 1) = r * (3 * B + 1) + (3 * B + 1) := by ring
                omega
              nlinarith
            calc 2 * k * (q * N0) = (2 * k * q) * N0 := by ring
              _ ≤ (p * (q + (3 * B + 1))) * N0 := by gcongr
              _ = p * ((q + (3 * B + 1)) * N0) := by ring
        _ ≤ p * (2 * k * N1) := by gcongr
        _ = 2 * k * (p * N1) := by ring
        _ ≤ 2 * k * (2 * k * N2) := by gcongr
  have h := main r hc hr
  have h3 : k * ncount (3 * k + 1) a c ≤ 2 * k * ncount (3 * k + 1) a (c + r) :=
    le_trans (by gcongr; omega) h
  refine Nat.le_of_mul_le_mul_left (c := k) ?_ hk
  calc k * ncount (3 * k + 1) a c ≤ 2 * k * ncount (3 * k + 1) a (c + r) := h3
    _ = k * (2 * ncount (3 * k + 1) a (c + r)) := by ring

/-- a single value has at most the fraction `2/(R+1)` of all words -/
theorem ncount_le (k j R c : ℕ) (a : Fin 3) (hc : c ≤ k + j) (hk : 0 < k)
    (hR : R * (3 * (j + R) + 1) ≤ k) :
    (R + 1) * ncount (3 * k + 1) a c ≤ 2 * 3 ^ (3 * k + 1) := by
  have h1 : ∀ r ∈ Finset.range (R + 1),
      ncount (3 * k + 1) a c ≤ 2 * ncount (3 * k + 1) a (c + r) := by
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    refine ncount_add k (j + R) c r a (by omega) hk (le_trans ?_ hR)
    gcongr
  calc (R + 1) * ncount (3 * k + 1) a c = ∑ _r ∈ Finset.range (R + 1), ncount (3 * k + 1) a c := by
        simp
    _ ≤ ∑ r ∈ Finset.range (R + 1), 2 * ncount (3 * k + 1) a (c + r) := Finset.sum_le_sum h1
    _ = 2 * ∑ r ∈ Finset.range (R + 1), ncount (3 * k + 1) a (c + r) := by rw [Finset.mul_sum]
    _ = 2 * ∑ c' ∈ (Finset.range (R + 1)).map (addLeftEmbedding c), ncount (3 * k + 1) a c' := by
        rw [Finset.sum_map]; rfl
    _ ≤ 2 * 3 ^ (3 * k + 1) := by gcongr; exact sum_ncount_le _ _ _

/-- B3: the window `[k - j, k + j]` contains a small fraction of the words, for large `k` -/
theorem window_le (j : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℕ, ∀ k ≥ K, ∀ a : Fin 3,
    ((#{w : Word (3 * k + 1) | k ≤ cnt1 a w + j ∧ cnt1 a w ≤ k + j} : ℕ) : ℝ)
      ≤ δ * 3 ^ (3 * k + 1) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (2 * (2 * j + 1) / δ)
  refine ⟨R * (3 * (j + R) + 1) + 1, fun k hk a => ?_⟩
  have hk0 : 0 < k := by omega
  have hkR : R * (3 * (j + R) + 1) ≤ k := by omega
  have hsub : ({w : Word (3 * k + 1) | k ≤ cnt1 a w + j ∧ cnt1 a w ≤ k + j} : Finset _)
      ⊆ (Finset.Icc (k - j) (k + j)).biUnion
        (fun c => ({w : Word (3 * k + 1) | cnt1 a w = c} : Finset _)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨cnt1 a w, ⟨by omega, by omega⟩, rfl⟩
  have hcard : #{w : Word (3 * k + 1) | k ≤ cnt1 a w + j ∧ cnt1 a w ≤ k + j}
      ≤ ∑ c ∈ Finset.Icc (k - j) (k + j), ncount (3 * k + 1) a c :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hreal : ∀ c ∈ Finset.Icc (k - j) (k + j),
      (ncount (3 * k + 1) a c : ℝ) ≤ 2 * 3 ^ (3 * k + 1) / (R + 1) := by
    intro c hc
    have h := ncount_le k j R c a (Finset.mem_Icc.mp hc).2 hk0 hkR
    have h' : ((R : ℝ) + 1) * ncount (3 * k + 1) a c ≤ 2 * 3 ^ (3 * k + 1) := by exact_mod_cast h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hnum : ((#(Finset.Icc (k - j) (k + j)) : ℕ) : ℝ) ≤ 2 * j + 1 := by
    rw [Nat.card_Icc]
    have : k + j + 1 - (k - j) ≤ 2 * j + 1 := by omega
    exact_mod_cast this
  calc ((#{w : Word (3 * k + 1) | k ≤ cnt1 a w + j ∧ cnt1 a w ≤ k + j} : ℕ) : ℝ)
      ≤ ∑ c ∈ Finset.Icc (k - j) (k + j), (ncount (3 * k + 1) a c : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _c ∈ Finset.Icc (k - j) (k + j), (2 * 3 ^ (3 * k + 1) / (R + 1) : ℝ) :=
        Finset.sum_le_sum hreal
    _ = #(Finset.Icc (k - j) (k + j)) * (2 * 3 ^ (3 * k + 1) / (R + 1) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * j + 1) * (2 * 3 ^ (3 * k + 1) / (R + 1) : ℝ) := by gcongr
    _ = (2 * (2 * j + 1) / (R + 1)) * 3 ^ (3 * k + 1) := by ring
    _ ≤ δ * 3 ^ (3 * k + 1) := by
        gcongr
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hR
        nlinarith


end RankRings

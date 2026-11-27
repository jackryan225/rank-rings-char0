module

public import RankRings.Words

@[expose] public section
/-! The off-diagonal block of a tensor power, in matrix form.
`X C^{⊗m} Y = l^{j+1} Q + R * W`, where `W` is the diagonal projection on the words of `Y`
with fewer than `k + j` letters in `I` (a window). Mathlib only. -/

open Finset

namespace RankRings

variable {R : Type*} [CommRing R] {m : ℕ}

/-- diagonal `0/1` matrix of a set of words -/
def dg (X : Finset (Word m)) : Matrix (Word m) (Word m) R :=
  Matrix.diagonal fun w => if w ∈ X then 1 else 0

theorem offblock (I J : Finset (Fin 3)) (C : Matrix (Fin 3) (Fin 3) R) (l : R)
    (h : ∀ i j, j ∈ I → i ∉ J → l ∣ C i j) (k j : ℕ) (X Y : Finset (Word m))
    (hX : ∀ w ∈ X, cnt J w < k) (hY : ∀ w ∈ Y, k ≤ cnt I w) :
    ∃ Q Rm : Matrix (Word m) (Word m) R,
      dg X * tpow m C * dg Y = l ^ (j + 1) • Q + Rm * dg (Y.filter fun w => cnt I w < k + j) := by
  classical
  set Yb := Y.filter fun w => ¬ cnt I w < k + j
  set Yw := Y.filter fun w => cnt I w < k + j
  have hsplit : (dg Y : Matrix (Word m) (Word m) R) = dg Yb + dg Yw := by
    ext w w'
    by_cases hww : w = w'
    · subst hww
      by_cases hy : w ∈ Y <;> by_cases hc : cnt I w < k + j <;> simp [dg, Yb, Yw, hy, hc]
    · simp [dg, Matrix.diagonal_apply_ne _ hww]
  have hdiv : ∀ w w', l ^ (j + 1) ∣ (dg X * tpow m C * dg Yb : Matrix (Word m) (Word m) R) w w' := by
    intro w w'
    simp only [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hw : w ∈ X
    · by_cases hw' : w' ∈ Yb
      · simp only [hw, hw', if_true, one_mul, mul_one]
        have hw'' : w' ∈ Y ∧ ¬ cnt I w' < k + j := by simpa [Yb] using hw'
        exact dvd_tpow I J C l h w w' k j (by omega) (hX w hw)
      · simp [hw']
    · simp [hw]
  refine ⟨Matrix.of fun w w' => Classical.choose (hdiv w w'), dg X * tpow m C, ?_⟩
  rw [hsplit, Matrix.mul_add]
  congr 1
  ext w w'
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact Classical.choose_spec (hdiv w w')

end RankRings

end

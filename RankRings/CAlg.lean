module

public import Mathlib

@[expose] public section
/-!
# The algebraic closure of `ℚ_[p]` is isomorphic (as a ring) to `ℂ`

Both fields are algebraically closed, of characteristic zero, and of cardinality continuum.
-/

open Cardinal

namespace RankRings

theorem mk_padic_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  change #(CauSeq.Completion.Cauchy (padicNorm p)) ≤ 𝔠
  unfold CauSeq.Completion.Cauchy
  apply mk_quotient_le.trans
  apply (mk_subtype_le _).trans_eq
  rw [← power_def, mk_nat, Cardinal.mkRat, aleph0_power_aleph0]

theorem mk_padic (p : ℕ) [Fact p.Prime] : #ℚ_[p] = 𝔠 :=
  le_antisymm (mk_padic_le p) (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])

theorem mk_padicAlgCl (p : ℕ) [Fact p.Prime] : #(PadicAlgCl p) = 𝔠 := by
  apply le_antisymm
  · have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    rw [mk_padic p, max_eq_left aleph0_le_continuum] at h
    exact h
  · rw [← mk_padic p]
    exact mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

theorem nonempty_padicAlgCl_equiv_complex (p : ℕ) [Fact p.Prime] :
    Nonempty (PadicAlgCl p ≃+* ℂ) := by
  apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
  · rw [mk_padicAlgCl p]; exact aleph0_lt_continuum
  · rw [← Cardinal.eq, mk_padicAlgCl p, Cardinal.mk_complex]

end RankRings

end

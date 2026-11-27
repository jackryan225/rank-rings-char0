module

public import RankRings.Main
public import RankRings.NoHomF
public import RankRings.CAlg

@[expose] public section
/-!
# Final forms: all fields of characteristic zero, a `ℂ`-algebra, and the finite `ε` form
-/

open Matrix Filter

namespace RankRings

theorem no_config_RUF {σ : Pt ≃ Pt} {I : Type} (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type)
    [∀ i, Field (F i)] [∀ i, CharZero (F i)] (hd : ∀ i, 0 < d i) (c : Config (Gen.RUF ω d F) σ) :
    False :=
  Gen.no_config σ (by rw [order_Pt]) hd c.f c.g c.x c.y c.h1 c.h2 c.h3 c.h4

/-- **Main theorem** (countable form, matrix rings over arbitrary fields of characteristic zero). -/
theorem main_countable_char0 : ∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧
    IsVNRegular S ∧ ∃ rk : S → ℝ, IsRankFunction rk ∧
      ∀ (I : Type) (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
        [∀ i, CharZero (F i)], (∀ i, 0 < d i) → IsEmpty (S →+* Gen.RUF ω d F) := by
  obtain ⟨σ, S, instR, instA, h1, h2, ⟨rk, h3⟩, ⟨c⟩⟩ := main_core
  exact ⟨S, instR, instA, h1, h2, rk, h3, fun I ω d F _ _ hd => ⟨fun φ => no_config_RUF ω d F hd (c.map φ)⟩⟩

/-- **Main theorem** (`ℂ`-algebra form). -/
theorem main_complex : ∃ (S : Type) (_ : Ring S) (_ : Algebra ℂ S), IsVNRegular S ∧
    ∃ rk : S → ℝ, IsRankFunction rk ∧
      ∀ (I : Type) (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
        [∀ i, CharZero (F i)], (∀ i, 0 < d i) → IsEmpty (S →+* Gen.RUF ω d F) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_Pt
  obtain ⟨e⟩ := nonempty_padicAlgCl_equiv_complex 7
  let K := PadicAlgCl 7
  let R := RR K WI hyp
  let φ : ℂ →+* R := (RingCon.mk' _).comp ((algebraMap K (tight K WI hyp)).comp e.symm.toRingHom)
  let alg : Algebra ℂ R := RingHom.toAlgebra' φ (fun z x => scalar_central K (e.symm z) x)
  let c := configRR K σ hσ
  exact ⟨R, inferInstance, alg, isVNRegular_RR K, rk K WI hyp, isRankFunction_RR K,
    fun I ω d F _ _ hd => ⟨fun ψ => no_config_RUF ω d F hd (c.map ψ)⟩⟩

end RankRings

end

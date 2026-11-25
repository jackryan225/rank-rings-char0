import Challenge.Statement
import RankRings.NoHomF

/-!
# Sanity checks of the definitions in `Challenge/Statement.lean`

These lemmas show that the three statements are not true for a trivial reason, such as a target ring
that is always zero or a target class that admits no homomorphisms at all.

* `quotient_eq`: the congruence of `RankUltraproduct` is exactly "`a - b` has normalized rank tending to
  `0` along `ω`". So `RankUltraproduct ω d F` is `∏ M_{d i}(F i) / J` with
  `J = {a | rank (a i) / d i → 0 along ω}`.
* `ultra_ne_zero`: if all sizes are positive, the rank ultraproduct is not the zero ring.
* `field_example`: every field, with rank `0` at `0` and `1` elsewhere, is a von Neumann regular ring
  with a rank function in the sense of `IsRankFunction`.
* `rat_maps`: the countable regular rank `ℚ`-algebra `ℚ` has a unital ring homomorphism into every rank
  ultraproduct of matrix rings over fields of characteristic zero. So the conclusion of `elek_countable`
  is a property that some countable regular rank `ℚ`-algebras do not have.
* `complex_maps`: the regular rank `ℂ`-algebra `ℂ` has a unital ring homomorphism into every rank
  ultraproduct of complex matrix rings (compare `elek_complex`).
* `matrix_maps`: the matrix ring `M_2(ℚ)` has a unital ring homomorphism into every rank ultraproduct of
  the matrix rings `M_{2 k i}(F i)`.

The file imports `Challenge/Statement.lean` only for the definitions. The proofs below do not use the
three theorems of that file (they are `sorry` there); `#print axioms` at the end shows this.
-/

open RankRingsChallenge

namespace RankRingsSanity

section Ultra

variable {I : Type} (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]

/-- The congruence of `RankUltraproduct` is the congruence "differ by a rank-null sequence". -/
theorem quotient_eq :
    ringConGen (fun a b : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (F i)) => IsRankNull ω d F (a - b)) =
      RankRings.Gen.rnullCon ω d F := by
  apply le_antisymm
  · rw [RingCon.ringConGen_le]
    intro a b h
    exact h
  · intro a b h
    exact RingConGen.Rel.of _ _ h

/-- The map from `RankUltraproduct` to the quotient by the explicit congruence. -/
noncomputable def toRUF : RankUltraproduct ω d F →+* RankRings.Gen.RUF ω d F :=
  RingCon.lift _ (RingCon.mk' (RankRings.Gen.rnullCon ω d F)) (by
    rw [RingCon.ringConGen_le, RingCon.ker_mk'_eq]
    intro a b h
    exact h)

/-- With positive sizes the rank ultraproduct is not the zero ring. -/
theorem ultra_ne_zero (hd : ∀ i, 0 < d i) : (1 : RankUltraproduct ω d F) ≠ 0 := by
  intro h
  have h1 := congrArg (toRUF ω d F) h
  rw [map_one, map_zero, ← map_one (RingCon.mk' (RankRings.Gen.rnullCon ω d F)),
    ← map_zero (RingCon.mk' (RankRings.Gen.rnullCon ω d F)), RankRings.Gen.mk_eq_iff, sub_zero] at h1
  unfold RankRings.Gen.IsRNull at h1
  have h2 : Filter.Tendsto (fun _ : I => (1 : ℝ)) (ω : Filter I) (nhds 0) := by
    refine Filter.Tendsto.congr (fun i => ?_) h1
    have hi : (d i : ℝ) ≠ 0 := by exact_mod_cast (hd i).ne'
    simp [hi]
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h2)

/-- `ℚ` maps unitally into every rank ultraproduct over fields of characteristic zero. -/
noncomputable def ratHom [∀ i, CharZero (F i)] : ℚ →+* RankUltraproduct ω d F :=
  (RingCon.mk' _).comp (algebraMap ℚ (∀ i, Matrix (Fin (d i)) (Fin (d i)) (F i)))

/-- `M_2(ℚ)` maps unitally into every rank ultraproduct of the rings `M_{2 k i}(F i)`. -/
noncomputable def matHom [∀ i, CharZero (F i)] (k : I → ℕ) :
    Matrix (Fin 2) (Fin 2) ℚ →+* RankUltraproduct ω (fun i => 2 * k i) F :=
  (RingCon.mk' _).comp (RingHom.pi fun i =>
    ((Matrix.reindexRingEquiv (F i) finProdFinEquiv).toRingHom.comp
      ((Matrix.blockDiagonalRingHom (m := Fin 2) (o := Fin (k i)) (α := F i)).comp
        ((Pi.constRingHom (Fin (k i)) _).comp (algebraMap ℚ (F i)).mapMatrix))))

end Ultra

open Classical in
/-- A field with the rank `0` at `0` and `1` elsewhere is a regular ring with a rank function. -/
theorem field_example (K : Type*) [Field K] :
    IsVNRegular K ∧ IsRankFunction (fun x : K => if x = 0 then (0 : ℝ) else 1) := by
  refine ⟨fun a => ⟨a⁻¹, ?_⟩, ?_⟩
  · by_cases h : a = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  constructor
  · intro x; split_ifs <;> norm_num
  · intro x; split_ifs <;> norm_num
  · simp
  · intro x; split_ifs with h <;> simp [h]
  · intro x y
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy] <;> split_ifs <;> norm_num
  · intro x y
    by_cases hx : x = 0 <;> simp [hx] <;> split_ifs <;> norm_num
  · intro x y
    by_cases hy : y = 0 <;> simp [hy] <;> split_ifs <;> norm_num
  · intro e f _ _ hef _
    rcases mul_eq_zero.mp hef with h | h <;> simp [h]

/-- `ℚ` is a countable regular rank `ℚ`-algebra that maps unitally into every rank ultraproduct of
matrix rings over fields of characteristic zero, and these targets are not zero rings. This is the
statement `elek_countable` with `IsEmpty` replaced by its negation. -/
theorem rat_maps : ∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
    ∃ rk : S → ℝ, IsRankFunction rk ∧
      ∀ (I : Type) (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
        [∀ i, CharZero (F i)], (∀ i, 0 < d i) →
          Nonempty (S →+* RankUltraproduct ω d F) ∧ (1 : RankUltraproduct ω d F) ≠ 0 :=
  ⟨ℚ, inferInstance, inferInstance, inferInstance, (field_example ℚ).1, _, (field_example ℚ).2,
    fun I ω d F _ _ hd => ⟨⟨ratHom ω d F⟩, ultra_ne_zero ω d F hd⟩⟩

/-- `ℂ` is a regular rank `ℂ`-algebra that maps unitally into every rank ultraproduct of complex
matrix rings (compare `elek_complex`). -/
theorem complex_maps : ∃ (S : Type) (_ : Ring S) (_ : Algebra ℂ S), IsVNRegular S ∧
    ∃ rk : S → ℝ, IsRankFunction rk ∧
      ∀ (I : Type) (ω : Ultrafilter I) (d : I → ℕ), (∀ i, 0 < d i) →
        Nonempty (S →+* RankUltraproduct ω d (fun _ => ℂ)) ∧
          (1 : RankUltraproduct ω d (fun _ => ℂ)) ≠ 0 :=
  ⟨ℂ, inferInstance, inferInstance, (field_example ℂ).1, _, (field_example ℂ).2,
    fun I ω d hd => ⟨⟨(RingCon.mk' _).comp (algebraMap ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ))⟩,
      ultra_ne_zero ω d _ hd⟩⟩

/-- `M_2(ℚ)` (a countable regular ring with the rank function `rank / 2`) maps unitally into rank
ultraproducts of matrix rings, which are not zero rings when all `k i` are positive. -/
theorem matrix_maps {I : Type} (ω : Ultrafilter I) (k : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
    [∀ i, CharZero (F i)] (hk : ∀ i, 0 < k i) :
    Nonempty (Matrix (Fin 2) (Fin 2) ℚ →+* RankUltraproduct ω (fun i => 2 * k i) F) ∧
      (1 : RankUltraproduct ω (fun i => 2 * k i) F) ≠ 0 :=
  ⟨⟨matHom ω F k⟩, ultra_ne_zero ω _ F fun i => Nat.mul_pos (by norm_num) (hk i)⟩

end RankRingsSanity

#print axioms RankRingsSanity.quotient_eq
#print axioms RankRingsSanity.ultra_ne_zero
#print axioms RankRingsSanity.rat_maps
#print axioms RankRingsSanity.complex_maps
#print axioms RankRingsSanity.matrix_maps

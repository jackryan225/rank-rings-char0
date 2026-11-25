import RankRings.FiniteForm
import RankRings.NoHomF

/-!
# The finite `ε` form over every field of characteristic zero (paper Corollary B(ii), `ℓ = 7`)

One `ε > 0` works for all fields `F` of characteristic `0` at once (in `Type`), all sizes `N ≥ 1`.
Proof: by contradiction, with a rank ultraproduct of `M_{N k}(F k)` over the hyperfilter on `ℕ`,
where the field `F k` varies with `k`, and `Gen.no_config`.
-/

open Matrix Filter

namespace RankRings

/-- The `ε` statement for any `σ`, uniformly over all fields of characteristic `0`. -/
theorem eps_char0 (σ : Pt ≃ Pt) : ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type) [Field F] [CharZero F] (N : ℕ),
    0 < N → ∀ A : Gens → Matrix (Fin N) (Fin N) F, ∃ j, ε * N < ((ev A (rel σ j)).rank : ℝ) := by
  by_contra hne
  have hk : ∀ k : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (N : ℕ), 0 < N ∧
      ∃ A : Gens → Matrix (Fin N) (Fin N) F,
        ∀ j, ((ev A (rel σ j)).rank : ℝ) ≤ 1 / ((k : ℝ) + 1) * N := by
    intro k
    by_contra h
    apply hne
    refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
    intro F _ _ N hN A
    by_contra h2
    exact h ⟨F, inferInstance, inferInstance, N, hN, A, fun j => not_lt.1 fun hj => h2 ⟨j, hj⟩⟩
  choose F instF instC N hN A hA using hk
  let a : Gens → Gen.RUF hyp N F := fun g => RingCon.mk' _ (fun k => A k g)
  have c : Config (Gen.RUF hyp N F) σ := configOfRel (σ := σ) a fun j => by
    have e := ev_map (RingCon.mk' (Gen.rnullCon hyp N F)) (fun g k => A k g) (rel σ j)
    rw [show a = fun g => RingCon.mk' (Gen.rnullCon hyp N F) (fun k => A k g) from rfl, ← e,
      ← map_zero (RingCon.mk' (Gen.rnullCon hyp N F)), Gen.mk_eq_iff, sub_zero]
    have hev : ∀ k, (ev (fun g => fun k => A k g) (rel σ j)) k = ev (A k) (rel σ j) := by
      intro k
      exact ev_map (Pi.evalRingHom (fun k => Matrix (Fin (N k)) (Fin (N k)) (F k)) k)
        (fun g => fun k => A k g) (rel σ j)
    unfold Gen.IsRNull
    have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) (hyp : Filter ℕ) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left
        (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_)
      (fun k => ?_)
    · positivity
    · simp only [hev]
      have hNk : (0 : ℝ) < N k := by exact_mod_cast hN k
      rw [div_le_iff₀ hNk]
      exact hA k j
  exact Gen.no_config σ (by rw [order_Pt]) hN c.f c.g c.x c.y c.h1 c.h2 c.h3 c.h4

/-- **Finite form over every field of characteristic `0`** (Corollary B(ii) for `ℓ = 7`, presentation
with one generator `g_e` per edge): finitely many integer relations, exactly solvable in a countable
regular rank `ℚ`-algebra, and one `ε > 0` such that for EVERY field `F` of characteristic `0`, every
`N ≥ 1` and all `N × N` matrices over `F`, some relation has rank `> ε N`. -/
theorem finite_form_char0 : ∃ (Gn Rl : Type) (_ : Fintype Gn) (_ : Fintype Rl)
    (rel : Rl → FreeAlgebra ℤ Gn) (ε : ℝ), 0 < ε ∧
    (∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
      (∃ rk : S → ℝ, IsRankFunction rk) ∧ ∃ x : Gn → S, ∀ j, FreeAlgebra.lift ℤ x (rel j) = 0) ∧
    ∀ (F : Type) [Field F] [CharZero F] (N : ℕ), 0 < N → ∀ A : Gn → Matrix (Fin N) (Fin N) F,
      ∃ j, ε * N < ((FreeAlgebra.lift ℤ A (rel j)).rank : ℝ) := by
  obtain ⟨σ, S, i1, i2, h1, h2, h3, ⟨c⟩⟩ := main_core
  obtain ⟨ε, hε, hH⟩ := eps_char0 σ
  refine ⟨Gens, Rl σ, inferInstance, inferInstance, rel σ, ε, hε,
    ⟨S, i1, i2, h1, h2, h3, c.toGen, fun j => by rw [lift_eq_ev]; exact rel_of_config c j⟩,
    fun F _ _ N hN A => ?_⟩
  obtain ⟨j, hj⟩ := hH F N hN A
  exact ⟨j, by rw [lift_eq_ev]; exact hj⟩

/-- Sanity check: the new statement implies the old `ℂ` statement `finite_form` verbatim. -/
theorem finite_form_of_char0 : ∃ (Gn Rl : Type) (_ : Fintype Gn) (_ : Fintype Rl)
    (rel : Rl → FreeAlgebra ℤ Gn) (ε : ℝ), 0 < ε ∧
    (∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
      (∃ rk : S → ℝ, IsRankFunction rk) ∧ ∃ x : Gn → S, ∀ j, FreeAlgebra.lift ℤ x (rel j) = 0) ∧
    ∀ N : ℕ, 0 < N → ∀ A : Gn → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((FreeAlgebra.lift ℤ A (rel j)).rank : ℝ) := by
  obtain ⟨Gn, Rl, i1, i2, r, ε, hε, hS, hF⟩ := finite_form_char0
  exact ⟨Gn, Rl, i1, i2, r, ε, hε, hS, fun N hN A => hF ℂ N hN A⟩

/-! ### The paper's presentation: generators `f_p, x_{e,i}, y_{e,i}` (no `g_e`)

Relations (paper (eq:rel)): `f_p² = f_p`, `f_p x_{e,i} = x_{e,i}`, `f_{p'} x_{e,i} = 0`,
`∑_i y_{e,i} x_{e,i} = 1` for `e = (p,p')`, `p ∈ σ p'`. In a regular ring a solution gives a
`Config` (`g_e` := a left identity of `x_{e,0}, x_{e,1}, x_{e,2}` inside the right ideal they span). -/

/-- Evaluation of integer noncommutative polynomials in any generator type. -/
noncomputable def evG {G T : Type*} [Ring T] (x : G → T) : FreeAlgebra ℤ G →+* T :=
  (FreeAlgebra.lift ℤ x).toRingHom

lemma lift_eq_evG {G T : Type*} [Ring T] [inst : Algebra ℤ T] (x : G → T) (t : FreeAlgebra ℤ G) :
    FreeAlgebra.lift ℤ (A := T) x t = evG x t := by
  have : inst = Ring.toIntAlgebra T := Subsingleton.elim _ _
  subst this
  rfl

lemma evG_ι {G T : Type*} [Ring T] (x : G → T) (a : G) : evG x (FreeAlgebra.ι ℤ a) = x a := by
  simp [evG]

lemma evG_map {G R T : Type*} [Ring R] [Ring T] (φ : R →+* T) (x : G → R)
    (t : FreeAlgebra ℤ G) : φ (evG x t) = evG (fun a => φ (x a)) t := by
  have : (φ.toIntAlgHom).comp (FreeAlgebra.lift ℤ x) = FreeAlgebra.lift ℤ (fun a => φ (x a)) := by
    apply FreeAlgebra.hom_ext
    funext a
    simp
  exact congrArg (fun F => F t) this

/-- Generators of the paper: `f_p`, `x_{(p,p'),i}`, `y_{(p,p'),i}`. -/
abbrev GensP := Pt ⊕ (Pt × Pt × Fin 3) ⊕ (Pt × Pt × Fin 3)

/-- The edges `E = {(p,p') | p ∈ σ p'}`. -/
abbrev Edge (σ : Pt ≃ Pt) := {pp : Pt × Pt // pp.1 ∈ σ pp.2}

/-- Relation labels of the paper's presentation. -/
abbrev RlP (σ : Pt ≃ Pt) := Pt ⊕ (Edge σ × Fin 3) ⊕ (Edge σ × Fin 3) ⊕ Edge σ

noncomputable instance (σ : Pt ≃ Pt) : Fintype (RlP σ) := Fintype.ofFinite _

/-- generators of the paper's presentation in the free algebra -/
noncomputable abbrev XP (a : GensP) : FreeAlgebra ℤ GensP := FreeAlgebra.ι ℤ a

/-- The relations (eq:rel) of `B_7` exactly as in the paper. -/
noncomputable def relP (σ : Pt ≃ Pt) : RlP σ → FreeAlgebra ℤ GensP
  | .inl p => XP (.inl p) * XP (.inl p) - XP (.inl p)
  | .inr (.inl ⟨⟨(p, p'), _⟩, i⟩) =>
    XP (.inl p) * XP (.inr (.inl (p, p', i))) - XP (.inr (.inl (p, p', i)))
  | .inr (.inr (.inl ⟨⟨(p, p'), _⟩, i⟩)) => XP (.inl p') * XP (.inr (.inl (p, p', i)))
  | .inr (.inr (.inr ⟨(p, p'), _⟩)) =>
    ∑ i : Fin 3, XP (.inr (.inr (p, p', i))) * XP (.inr (.inl (p, p', i))) - 1

/-- In a regular ring: elements `x_i` (`i ∈ s`) with `u x_i = x_i`, `v x_i = 0` have a common left
identity `e` with `u e = e`, `v e = 0`. -/
lemma exists_left_id {R : Type*} [Ring R] (hreg : ∀ a : R, ∃ b, a * b * a = a) (u v : R)
    {ι : Type*} (s : Finset ι) (x : ι → R) (hu : ∀ i ∈ s, u * x i = x i)
    (hv : ∀ i ∈ s, v * x i = 0) : ∃ e : R, u * e = e ∧ v * e = 0 ∧ ∀ i ∈ s, e * x i = x i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | insert k s hk ih =>
    obtain ⟨e, he1, he2, he3⟩ := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      (fun i hi => hv i (Finset.mem_insert_of_mem hi))
    have hxu := hu k (Finset.mem_insert_self _ _)
    have hxv := hv k (Finset.mem_insert_self _ _)
    obtain ⟨b, hb⟩ : ∃ b, b = x k - e * x k := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ := hreg b
    have hub : u * b = b := by rw [hb, mul_sub, hxu, ← mul_assoc, he1]
    have hvb : v * b = 0 := by rw [hb, mul_sub, hxv, ← mul_assoc, he2, zero_mul, sub_zero]
    refine ⟨e + b * q - b * q * e, ?_, ?_, ?_⟩
    · have : u * (e + b * q - b * q * e) = u * e + u * b * q - u * b * q * e := by noncomm_ring
      rw [this, he1, hub]
    · have : v * (e + b * q - b * q * e) = v * e + v * b * q - v * b * q * e := by noncomm_ring
      rw [this, he2, hvb]
      simp
    · intro i hi
      rcases Finset.mem_insert.1 hi with h | hi
      · rw [h]
        calc (e + b * q - b * q * e) * x k = e * x k + b * q * (x k - e * x k) := by noncomm_ring
          _ = x k := by rw [← hb, hq, hb]; abel
      · have h3 := he3 i hi
        calc (e + b * q - b * q * e) * x i = e * x i + b * q * x i - b * q * (e * x i) := by
              noncomm_ring
          _ = x i := by rw [h3]; abel

/-- A solution of the paper's relations in a regular ring gives a configuration. -/
lemma config_of_relP {R : Type*} [Ring R] (hreg : ∀ a : R, ∃ b, a * b * a = a) {σ : Pt ≃ Pt}
    (a : GensP → R) (h : ∀ j, evG a (relP σ j) = 0) : Nonempty (Config R σ) := by
  classical
  have hu : ∀ p p' (hp : p ∈ σ p') (i : Fin 3),
      a (.inl p) * a (.inr (.inl (p, p', i))) = a (.inr (.inl (p, p', i))) := fun p p' hp i => by
    have := h (.inr (.inl ⟨⟨(p, p'), hp⟩, i⟩))
    simp only [relP, XP, map_sub, map_mul, evG_ι] at this
    exact sub_eq_zero.1 this
  have hv : ∀ p p' (hp : p ∈ σ p') (i : Fin 3), a (.inl p') * a (.inr (.inl (p, p', i))) = 0 :=
    fun p p' hp i => by
    have := h (.inr (.inr (.inl ⟨⟨(p, p'), hp⟩, i⟩)))
    simpa only [relP, XP, map_mul, evG_ι] using this
  have hg : ∀ p p', ∃ e : R, p ∈ σ p' → a (.inl p) * e = e ∧ a (.inl p') * e = 0 ∧
      ∀ i : Fin 3, e * a (.inr (.inl (p, p', i))) = a (.inr (.inl (p, p', i))) := by
    intro p p'
    by_cases hp : p ∈ σ p'
    · obtain ⟨e, h1, h2, h3⟩ := exists_left_id hreg (a (.inl p)) (a (.inl p')) Finset.univ
        (fun i => a (.inr (.inl (p, p', i)))) (fun i _ => hu p p' hp i) (fun i _ => hv p p' hp i)
      exact ⟨e, fun _ => ⟨h1, h2, fun i => h3 i (Finset.mem_univ i)⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose g hg using hg
  exact ⟨{
    f := fun p => a (.inl p)
    g := g
    x := fun p p' i => a (.inr (.inl (p, p', i)))
    y := fun p p' i => a (.inr (.inr (p, p', i)))
    h1 := fun p => by
      have := h (.inl p)
      simp only [relP, XP, map_sub, map_mul, evG_ι] at this
      exact sub_eq_zero.1 this
    h2 := fun p p' hp => (hg p p' hp).1
    h3 := fun p p' hp => (hg p p' hp).2.1
    h4 := fun p p' hp => by
      have := h (.inr (.inr (.inr ⟨(p, p'), hp⟩)))
      simp only [relP, XP, map_sub, map_sum, map_mul, map_one, evG_ι] at this
      rw [← sub_eq_zero, ← this]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, (hg p p' hp).2.2 i] }⟩

/-- A configuration gives a solution of the paper's relations (`x_{e,i} := g_e x_i`). -/
lemma relP_of_config {R : Type*} [Ring R] {σ : Pt ≃ Pt} (c : Config R σ) (j : RlP σ) :
    evG (Sum.elim c.f (Sum.elim (fun t => c.g t.1 t.2.1 * c.x t.1 t.2.1 t.2.2)
      (fun t => c.y t.1 t.2.1 t.2.2))) (relP σ j) = 0 := by
  rcases j with p | ⟨⟨⟨p, p'⟩, hp⟩, i⟩ | ⟨⟨⟨p, p'⟩, hp⟩, i⟩ | ⟨⟨p, p'⟩, hp⟩
  · simp [relP, XP, evG_ι, c.h1 p]
  · simp [relP, XP, evG_ι, ← mul_assoc, c.h2 p p' hp]
  · simp [relP, XP, evG_ι, ← mul_assoc, c.h3 p p' hp]
  · simp only [relP, XP, map_sub, map_sum, map_mul, map_one, evG_ι, Sum.elim_inl, Sum.elim_inr]
    rw [sub_eq_zero, ← c.h4 p p' hp]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

/-- The rank ultraproduct over varying fields is von Neumann regular. -/
lemma regular_RUF {I : Type} (ω : Ultrafilter I) (d : I → ℕ) (F : I → Type) [∀ i, Field (F i)]
    (a : Gen.RUF ω d F) : ∃ b, a * b * a = a := by
  obtain ⟨A, rfl⟩ := RingCon.mk'_surjective (Gen.rnullCon ω d F) a
  exact ⟨RingCon.mk' _ (Gen.qP A), by rw [← map_mul, ← map_mul, Gen.qP_spec]⟩

/-- The `ε` statement for the paper's relations, any `σ`, all fields of characteristic `0`. -/
theorem eps_char0_paper (σ : Pt ≃ Pt) : ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type) [Field F] [CharZero F]
    (N : ℕ), 0 < N → ∀ A : GensP → Matrix (Fin N) (Fin N) F,
      ∃ j, ε * N < ((evG A (relP σ j)).rank : ℝ) := by
  by_contra hne
  have hk : ∀ k : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (N : ℕ), 0 < N ∧
      ∃ A : GensP → Matrix (Fin N) (Fin N) F,
        ∀ j, ((evG A (relP σ j)).rank : ℝ) ≤ 1 / ((k : ℝ) + 1) * N := by
    intro k
    by_contra h
    apply hne
    refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
    intro F _ _ N hN A
    by_contra h2
    exact h ⟨F, inferInstance, inferInstance, N, hN, A, fun j => not_lt.1 fun hj => h2 ⟨j, hj⟩⟩
  choose F instF instC N hN A hA using hk
  let a : GensP → Gen.RUF hyp N F := fun g => RingCon.mk' _ (fun k => A k g)
  obtain ⟨c⟩ := config_of_relP (σ := σ) (regular_RUF hyp N F) a fun j => by
    have e := evG_map (RingCon.mk' (Gen.rnullCon hyp N F)) (fun g k => A k g) (relP σ j)
    rw [show a = fun g => RingCon.mk' (Gen.rnullCon hyp N F) (fun k => A k g) from rfl, ← e,
      ← map_zero (RingCon.mk' (Gen.rnullCon hyp N F)), Gen.mk_eq_iff, sub_zero]
    have hev : ∀ k, (evG (fun g => fun k => A k g) (relP σ j)) k = evG (A k) (relP σ j) := by
      intro k
      exact evG_map (Pi.evalRingHom (fun k => Matrix (Fin (N k)) (Fin (N k)) (F k)) k)
        (fun g => fun k => A k g) (relP σ j)
    unfold Gen.IsRNull
    have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) (hyp : Filter ℕ) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left
        (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_)
      (fun k => ?_)
    · positivity
    · simp only [hev]
      have hNk : (0 : ℝ) < N k := by exact_mod_cast hN k
      rw [div_le_iff₀ hNk]
      exact hA k j
  exact Gen.no_config σ (by rw [order_Pt]) hN c.f c.g c.x c.y c.h1 c.h2 c.h3 c.h4

/-- **Corollary B(ii) for `ℓ = 7`, paper's presentation.** The relations (eq:rel) of `B_7`
(generators `f_p, x_{e,i}, y_{e,i}`) hold exactly in a countable regular rank `ℚ`-algebra, and
there is `ε > 0` such that for every field `F` of characteristic `0` (in `Type`), every `N ≥ 1`
and all `N × N` matrices over `F`, some relation has rank `> ε N`. -/
theorem finite_form_paper : ∃ σ : Pt ≃ Pt, (∀ p, p ∉ σ p) ∧ ∃ ε : ℝ, 0 < ε ∧
    (∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
      (∃ rk : S → ℝ, IsRankFunction rk) ∧
        ∃ x : GensP → S, ∀ j, FreeAlgebra.lift ℤ x (relP σ j) = 0) ∧
    ∀ (F : Type) [Field F] [CharZero F] (N : ℕ), 0 < N → ∀ A : GensP → Matrix (Fin N) (Fin N) F,
      ∃ j, ε * N < ((FreeAlgebra.lift ℤ A (relP σ j)).rank : ℝ) := by
  obtain ⟨σ, S, i1, i2, h1, h2, h3, ⟨c⟩⟩ := main_core
  -- `p ∈ σ p` would force `g = 0`, hence `1 = 0` in `S`, impossible with a rank function
  have hσ : ∀ p, p ∉ σ p := fun p hp => by
    obtain ⟨rk, hrk⟩ := h3
    have hg : c.g p p = 0 := by rw [← c.h2 p p hp, c.h3 p p hp]
    have h01 : (1 : S) = 0 := by rw [← c.h4 p p hp]; simp [hg]
    have h1' := hrk.map_one
    rw [h01, (hrk.eq_zero_iff 0).2 rfl] at h1'
    exact zero_ne_one h1'
  obtain ⟨ε, hε, hH⟩ := eps_char0_paper σ
  refine ⟨σ, hσ, ε, hε, ⟨S, i1, i2, h1, h2, h3, Sum.elim c.f (Sum.elim
    (fun t => c.g t.1 t.2.1 * c.x t.1 t.2.1 t.2.2) (fun t => c.y t.1 t.2.1 t.2.2)), fun j => by
    rw [lift_eq_evG]; exact relP_of_config c j⟩, fun F _ _ N hN A => ?_⟩
  obtain ⟨j, hj⟩ := hH F N hN A
  exact ⟨j, by rw [lift_eq_evG]; exact hj⟩

end RankRings

#print axioms RankRings.eps_char0
#print axioms RankRings.finite_form_char0
#print axioms RankRings.finite_form_of_char0
#print axioms RankRings.eps_char0_paper
#print axioms RankRings.finite_form_paper

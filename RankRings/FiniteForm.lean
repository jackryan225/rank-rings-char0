import RankRings.Main

/-!
# The finite form: integer relations with no `ε`-approximate complex matrix solutions
-/

open Matrix Filter

namespace RankRings

section rels

variable (σ : Pt ≃ Pt)

/-- Relation labels. -/
abbrev Rl := Pt ⊕ ({pp : Pt × Pt // pp.1 ∈ σ pp.2} × Fin 3)

noncomputable instance : Fintype (Rl σ) := Fintype.ofFinite _

/-- generators as elements of the free algebra -/
noncomputable abbrev X (a : Gens) : FreeAlgebra ℤ Gens := FreeAlgebra.ι ℤ a

/-- The relations of `B_7`. -/
noncomputable def rel : Rl σ → FreeAlgebra ℤ Gens
  | .inl p => X (.inl p) * X (.inl p) - X (.inl p)
  | .inr ⟨⟨(p, p'), _⟩, i⟩ =>
    ![X (.inl p) * X (.inr (.inl (p, p'))) - X (.inr (.inl (p, p'))),
      X (.inl p') * X (.inr (.inl (p, p'))),
      ∑ i : Fin 3, X (.inr (.inr (.inr (p, p', i)))) * X (.inr (.inl (p, p'))) *
        X (.inr (.inr (.inl (p, p', i)))) - 1] i

variable {σ}

/-- Evaluation of integer noncommutative polynomials (with the canonical `ℤ`-algebra structure). -/
noncomputable def ev {T : Type*} [Ring T] (x : Gens → T) : FreeAlgebra ℤ Gens →+* T :=
  (FreeAlgebra.lift ℤ x).toRingHom

lemma lift_eq_ev {T : Type*} [Ring T] [inst : Algebra ℤ T] (x : Gens → T) (t : FreeAlgebra ℤ Gens) :
    FreeAlgebra.lift ℤ (A := T) x t = ev x t := by
  have : inst = Ring.toIntAlgebra T := Subsingleton.elim _ _
  subst this
  rfl

lemma ev_ι {T : Type*} [Ring T] (x : Gens → T) (a : Gens) : ev x (FreeAlgebra.ι ℤ a) = x a := by
  simp [ev]

/-- The generators of a configuration. -/
def Config.toGen {T : Type*} [Ring T] (c : Config T σ) : Gens → T := fun a =>
  Sum.elim c.f (Sum.elim (fun pp => c.g pp.1 pp.2)
    (Sum.elim (fun t => c.x t.1 t.2.1 t.2.2) (fun t => c.y t.1 t.2.1 t.2.2))) a

lemma rel_of_config {T : Type*} [Ring T] (c : Config T σ) (j : Rl σ) :
    ev c.toGen (rel σ j) = 0 := by
  rcases j with p | ⟨⟨⟨p, p'⟩, h⟩, i⟩
  · simp [rel, X, ev_ι, Config.toGen, c.h1 p]
  · fin_cases i
    · simp [rel, X, ev_ι, Config.toGen, c.h2 p p' h]
    · simp [rel, X, ev_ι, Config.toGen, c.h3 p p' h]
    · simp [rel, X, ev_ι, Config.toGen, c.h4 p p' h]

/-- A solution of the relations is a configuration. -/
def configOfRel {T : Type*} [Ring T] (x : Gens → T)
    (h : ∀ j, ev x (rel σ j) = 0) : Config T σ where
  f p := x (.inl p)
  g p p' := x (.inr (.inl (p, p')))
  x p p' i := x (.inr (.inr (.inl (p, p', i))))
  y p p' i := x (.inr (.inr (.inr (p, p', i))))
  h1 p := by
    have := h (.inl p)
    simp only [rel, X, map_sub, map_mul, ev_ι] at this
    exact sub_eq_zero.1 this
  h2 p p' hp := by
    have := h (.inr ⟨⟨(p, p'), hp⟩, 0⟩)
    simp only [rel, X, Matrix.cons_val_zero, map_sub, map_mul, ev_ι] at this
    exact sub_eq_zero.1 this
  h3 p p' hp := by
    have := h (.inr ⟨⟨(p, p'), hp⟩, 1⟩)
    simpa [rel, X, ev_ι] using this
  h4 p p' hp := by
    have := h (.inr ⟨⟨(p, p'), hp⟩, 2⟩)
    simp only [rel, X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_sub, map_sum,
      map_mul, map_one, ev_ι] at this
    exact sub_eq_zero.1 this

end rels

lemma ev_map {R T : Type*} [Ring R] [Ring T] (φ : R →+* T) (x : Gens → R)
    (t : FreeAlgebra ℤ Gens) : φ (ev x t) = ev (fun a => φ (x a)) t := by
  have : (φ.toIntAlgHom).comp (FreeAlgebra.lift ℤ x) = FreeAlgebra.lift ℤ (fun a => φ (x a)) := by
    apply FreeAlgebra.hom_ext
    funext a
    simp
  exact congrArg (fun F => F t) this

/-- **Finite form.** -/
theorem finite_form : ∃ (Gn Rl : Type) (_ : Fintype Gn) (_ : Fintype Rl)
    (rel : Rl → FreeAlgebra ℤ Gn) (ε : ℝ), 0 < ε ∧
    (∃ (S : Type) (_ : Ring S) (_ : Algebra ℚ S), Countable S ∧ IsVNRegular S ∧
      (∃ rk : S → ℝ, IsRankFunction rk) ∧ ∃ x : Gn → S, ∀ j, FreeAlgebra.lift ℤ x (rel j) = 0) ∧
    ∀ N : ℕ, 0 < N → ∀ A : Gn → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((FreeAlgebra.lift ℤ A (rel j)).rank : ℝ) := by
  obtain ⟨σ, S, i1, i2, h1, h2, h3, ⟨c⟩⟩ := main_core
  suffices H : ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, 0 < N → ∀ A : Gens → Matrix (Fin N) (Fin N) ℂ,
      ∃ j, ε * N < ((ev A (rel σ j)).rank : ℝ) by
    obtain ⟨ε, hε, hH⟩ := H
    refine ⟨Gens, Rl σ, inferInstance, inferInstance, rel σ, ε, hε,
      ⟨S, i1, i2, h1, h2, h3, c.toGen, fun j => by rw [lift_eq_ev]; exact rel_of_config c j⟩,
      fun N hN A => ?_⟩
    obtain ⟨j, hj⟩ := hH N hN A
    exact ⟨j, by rw [lift_eq_ev]; exact hj⟩
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
  -- the normalized rank tends to zero
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

end RankRings

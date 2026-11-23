import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.StrictDom

open Topology Filter

theorem exists_small_eq_zero (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ, (∀ (w : InfinitePlace E) a, w (y a) < δ) → y = 0 := by
  first
  | exact @_root_.GlobalTheory.SmallIntegerVanishing.main
  | exact _root_.GlobalTheory.SmallIntegerVanishing.main
  | (apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallIntegerVanishing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallIntegerVanishing.main ..)

theorem eventually_eq_one (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ)
    (x : InfinitePlace E → Fin j → Fin j → ℂ) (hx : ∀ w, (Matrix.of (x w)).det ≠ 0) :
    ∀ᶠ h in 𝓝 x, ∀ γ : Matrix (Fin j) (Fin j) E, (∀ y ∈ Λ, γ *ᵥ y ∈ Λ) →
      (∀ w : InfinitePlace E, Matrix.of (h w) = γ.map w.embedding * Matrix.of (x w)) → γ = 1 := by
  classical
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_eq_zero E j Λ hΛ.fg
  obtain ⟨s, hs⟩ := hΛ.fg
  have hev : ∀ᶠ h in 𝓝 x, ∀ y ∈ s, ∀ (w : InfinitePlace E) (a : Fin j),
      ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
        - w.embedding (y a)‖ < δ := by
    refine (Filter.eventually_all_finset s).2 fun y _ => Filter.eventually_all.2 fun w =>
      Filter.eventually_all.2 fun a => ?_
    have hc : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
        ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
          - w.embedding (y a)‖ := by
      have h1 : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) :=
        continuous_apply w
      exact (((continuous_apply a).comp
        ((h1.matrix_mul continuous_const).matrix_mulVec continuous_const)).sub continuous_const).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)), Matrix.one_mulVec]
    simpa using hδ
  filter_upwards [hev] with h hh γ hγ hw
  have hfix : ∀ y ∈ s, γ *ᵥ y = y := fun y hy => by
    have hyΛ : y ∈ Λ := hs ▸ Submodule.subset_span hy
    refine sub_eq_zero.1 (hsmall _ (Λ.sub_mem (hγ y hyΛ) hyΛ) fun w a => ?_)
    have := hh y hy w a
    rw [hw w, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)),
      Matrix.mul_one] at this
    rw [← InfinitePlace.norm_embedding_eq, Pi.sub_apply, map_sub, RingHom.map_mulVec]
    exact this
  have hspan : Submodule.span E (s : Set (Fin j → E)) = ⊤ := by
    have := hΛ.span_eq_top
    rwa [← hs, Submodule.span_span_of_tower] at this
  have hall : ∀ y, γ *ᵥ y = y := fun y => by
    have hy : y ∈ Submodule.span E (s : Set (Fin j → E)) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => simp
    | add y y' _ _ h h' => rw [Matrix.mulVec_add, h, h']
    | smul c y _ h => rw [Matrix.mulVec_smul, h]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

theorem exists_strictDomain : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → ∀ e : GL (Fin j) E → MatInf E j, (∀ γ w a b, e γ w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)) → ∀ S : Subgroup (GL (Fin j) E), (∀ γ ∈ S, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ ∀ g, 0 < detNorm E j g → ∃! γ : GL (Fin j) E, γ ∈ S ∧ e γ * g ∈ D := by
  intro E _ _ j Λ hΛ e he S hS
  have hof : ∀ γ w, Matrix.of (e γ w) = (γ : Matrix (Fin j) (Fin j) E).map w.embedding :=
    fun γ w => by ext a b; exact he γ w a b
  have hpos : ∀ γ (g : MatInf E j), 0 < detNorm E j g → 0 < detNorm E j (e γ * g) := fun γ g hg => by
    rw [MeanDual.detNorm_mul]
    refine mul_pos ((MeanDual.detNorm_pos_iff E j _).2 fun w => ?_) hg
    rw [hof, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  have hone : ∀ g : MatInf E j, e 1 * g = g := fun g => MeanDual.matInf_ext E j fun w => by
    rw [MeanDual.of_mul, hof]; simp
  have hmul : ∀ γ γ' (g : MatInf E j), e (γ * γ') * g = e γ * (e γ' * g) := fun γ γ' g =>
    MeanDual.matInf_ext E j fun w => by
      simp only [MeanDual.of_mul, hof, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  have hcont : ∀ γ, Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ =>
      (show InfinitePlace E → Fin j → Fin j → ℂ from (e γ * (show MatInf E j from g) : MatInf E j)) := fun γ =>
    continuous_pi fun w => (continuous_const.matrix_mul
      (show Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) from
        continuous_apply w) : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
          Matrix.of (e γ w) * Matrix.of (h w))
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  haveI : Countable (GL (Fin j) E) := Units.val_injective.countable
  let U : Set (InfinitePlace E → Fin j → Fin j → ℂ) := {g | 0 < detNorm E j g}
  have hU : MeasurableSet U := MeanDual.measurableSet_detNorm_pos E j
  letI : MulAction S U :=
    { smul := fun γ g => ⟨(e γ * (show MatInf E j from g.1) : MatInf E j), hpos γ g.1 g.2⟩
      one_smul := fun g => Subtype.ext (hone g.1)
      mul_smul := fun γ γ' g => Subtype.ext (hmul γ γ' g.1) }
  have hsm : ∀ (γ : S) (g : U), (γ • g).1 = (e γ * (show MatInf E j from g.1) : MatInf E j) :=
    fun _ _ => rfl
  have hc : ∀ γ : S, Continuous fun g : U => γ • g := fun γ =>
    ((hcont γ).comp continuous_subtype_val).subtype_mk _
  haveI : MeasurableConstSMul S U := ⟨fun γ => (hc γ).measurable⟩
  have hdisc : ∀ x : U, ∃ V ∈ 𝓝 x, ∀ γ : S, γ • x ∈ V → γ = 1 := fun x => by
    have h := eventually_eq_one E j Λ hΛ x.1 ((MeanDual.detNorm_pos_iff E j _).1 x.2)
    refine ⟨_, continuous_subtype_val.continuousAt.eventually h, fun γ hγ => ?_⟩
    refine Subtype.ext (Units.ext (hγ _ (fun y hy => (hS γ γ.2 y).2 hy) fun w => ?_))
    rw [← hof]; rfl
  have hfree : ∀ (γ : S) (x : U), γ • x = x → γ = 1 := fun γ x h => by
    obtain ⟨V, hV, hV'⟩ := hdisc x
    exact hV' γ (h.symm ▸ mem_of_mem_nhds hV)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := S) (X := U)
    (fun γ => (isClosed_eq (hc γ) continuous_id).measurableSet)
    (fun x => by
      obtain ⟨V, hV, hV'⟩ := hdisc x
      exact ⟨V, hV, fun γ hγ => by rw [hV' γ hγ, one_smul]⟩)
  refine ⟨Subtype.val '' D, hU.subtype_image hD, ?_, fun g hg => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · obtain ⟨γ, hγ⟩ := hcov ⟨g, hg⟩
    refine ⟨γ, ⟨γ.2, _, hγ, rfl⟩, ?_⟩
    rintro k ⟨hk, x, hx, hxe⟩
    have hx' : x = (⟨k, hk⟩ : S) • (⟨g, hg⟩ : U) := Subtype.ext hxe
    have := hu _ hγ (⟨k, hk⟩ * γ⁻¹) (by rw [mul_smul, inv_smul_smul, ← hx']; exact hx)
    exact congrArg Subtype.val (mul_inv_eq_one.1 (hfree _ _ this))

end GlobalTheory.StrictDom

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRegularFormsFiniteProjectiveSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraComapSpanEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackFormsIntersectionEqChartLocalizationStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_isBundle : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e he hr
  have hstab : ∀ I, ∀ c ∈ rB k K x I, ∀ w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W),
      (c : K) • w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W) := by
    intro I c hc w hw
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hw ⊢
    rw [map_smul]
    exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K _ p p).2.1 _ hw).2.2.2 c hc
  have key : ∀ i, Module.Finite (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) ∧
      Module.Projective (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) := by
    intro i
    obtain ⟨hf1, hf2, hf3⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
    haveI := hf2
    haveI := hf3
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.span_regularForms_finite_projective_smooth k K (rB k K x {i}) p W e he hr
    exact GlobalTheory.T.finite_projective_span_of_integralClosure' k F K (rA k x {i}) (rB k K x {i}) (fun y => Iff.rfl) hf1 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hx i) W _
      (hstab {i}) hB1 hB2
  refine ⟨fun i => ?_, fun i => (key i).2, fun I i hi => GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization k F K d x hx p W e I i hi⟩
  obtain ⟨hfin, -⟩ := key i
  obtain ⟨-, hf2, -⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
  haveI := hf2
  haveI : FiniteDimensional F K := hx.fin
  set S : Set W := ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) with hSdef
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hA : ∀ a : rA k x {i}, ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rw [Subalgebra.smul_def, ← algebraMap_smul K (a : F) w]
    exact hstab {i} _ (Subalgebra.algebraMap_mem (integralClosure (rA k x {i}) K) a) w hw
  have hspan : (Submodule.span (rA k x {i}) S).restrictScalars k =
      (omB k K (rB k K x {i}) p).comap (e.restrictScalars k) := by
    apply le_antisymm
    · intro y hy
      change y ∈ Submodule.span (rA k x {i}) S at hy
      change y ∈ S
      induction hy using Submodule.span_induction with
      | mem z hz => exact hz
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul a z _ hz => exact hA a z hz
    · exact fun y hy => Submodule.subset_span hy
  refine ⟨s, by rw [hs, hspan], ?_⟩
  have hK := GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top k K (rB k K x {i}) p W e he hr
  have hF := GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' k F K (rB k K x {i}) W S (hstab {i}) hK
  rw [eq_top_iff, ← hF, Submodule.span_le]
  intro w hw
  have : w ∈ Submodule.span (rA k x {i}) (s : Set W) := by rw [hs]; exact Submodule.subset_span hw
  exact Submodule.span_le_restrictScalars (rA k x {i}) F (s : Set W) this

end GlobalTheory.PD

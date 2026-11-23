import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem GraphAreaIntegral.continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem GraphAreaIntegral.proof (h : GraphAreaHolomorphic.Statement) : GraphAreaIntegral.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA g
  set G := graphPt e F with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := μH[((2 * d : ℕ) : ℝ)] with hμ
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := μH[((2 * d : ℕ) : ℝ)] with hν
  set J : EuclideanSpace ℂ (Fin d) → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian
    (fderiv ℝ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) with hJ
  have hJm : Measurable J := ENNReal.measurable_ofReal.comp
    (GraphAreaIntegral.continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ G))
  have hGc : ContinuousOn G A := (continuousOn_graphPt e hF.continuousOn).mono hAΩ
  let f : A → EuclideanSpace ℂ (Fin n) := fun a => G a
  have hfc : Continuous f := hGc.domRestrict
  have hf : MeasurableEmbedding f :=
    { injective := fun a b hab => Subtype.ext (graphPt_injective_of_graphBase e F hab)
      measurable := hfc.measurable
      measurableSet_image' := fun s hs => by
        have hs' : MeasurableSet (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) :=
          MeasurableSet.subtype_image hA hs
        have : f '' s = G '' (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) := by
          rw [Set.image_image]
        rw [this]
        exact hs'.image_of_continuousOn_injOn (hGc.mono (by rintro _ ⟨a, -, rfl⟩; exact a.2))
          (graphPt_injective_of_graphBase e F).injOn }
  set M : Measure A := (μ.withDensity J).comap ((↑) : A → EuclideanSpace ℂ (Fin d)) with hM
  have hmeas : ν.restrict (G '' A) = M.map f := by
    ext1 S hS
    have hpre : ((↑) : A → EuclideanSpace ℂ (Fin d)) '' (f ⁻¹' S) = A ∩ G ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
      · rintro ⟨hx, hxS⟩
        exact ⟨⟨x, hx⟩, hxS, rfl⟩
    have hmS : MeasurableSet (A ∩ G ⁻¹' S) := by
      rw [← hpre]
      exact MeasurableSet.subtype_image hA (hf.measurable hS)
    rw [Measure.restrict_apply hS, Measure.map_apply hf.measurable hS,
      (MeasurableEmbedding.subtype_coe hA).comap_apply, hpre, withDensity_apply _ hmS,
      Set.inter_comm S, ← Set.image_inter_preimage]
    exact h d m n e Ω F hΩ hF _ (Set.inter_subset_left.trans hAΩ) hmS
  calc ∫⁻ y in G '' A, g y ∂ν = ∫⁻ y, g y ∂(M.map f) := by rw [hmeas]
    _ = ∫⁻ a, g (f a) ∂M := hf.lintegral_map g
    _ = ∫⁻ x in A, g (G x) ∂(μ.withDensity J) := lintegral_subtype_comap hA (fun x => g (G x))
    _ = ∫⁻ x, g (G x) ∂((μ.restrict A).withDensity J) := by rw [restrict_withDensity hA]
    _ = ∫⁻ x in A, J x * g (G x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hJm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫⁻ x in A, g (G x) * J x ∂μ := by simp_rw [mul_comm]

end

end GroundTheory.Heights₂.Heights

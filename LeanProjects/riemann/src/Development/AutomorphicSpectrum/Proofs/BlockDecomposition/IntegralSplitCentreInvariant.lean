import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem lintegral_image_prod_Ico_of_invariant {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : X × ℝ ≃ₜ Z) (ν : Measure X) [SFinite ν] {h : Z → ENNReal} (hh : Measurable h)
    {k : X → ENNReal} (hk : ∀ x t, h (e (x, t)) = k x) (D : Set X) :
    ∫⁻ g in e '' (D ×ˢ Set.Ico (0 : ℝ) 1), h g ∂(Measure.map e (ν.prod volume)) =
      ∫⁻ x in D, k x ∂ν := by
  have hemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  rw [hemb.restrict_map, e.injective.preimage_image, hemb.lintegral_map, ← Measure.prod_restrict,
    lintegral_prod (fun p => h (e p)) (hh.comp e.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp [hk]

theorem lintegral_productDomain_norm_sq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure] (c : ENNReal), Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ φ : GA E a → ℂ, Continuous φ → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∫⁻ g in ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)), ‖φ g‖ₑ ^ 2 ∂(c • μ) = ∫⁻ x in RightCosetSpace.fundamentalDomain (rationalGLOne E a), ‖φ (x : GA E a)‖ₑ ^ 2 ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hmap φ hc hinv
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hF : (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = ⇑e :=
    funext fun p => (he p.1 p.2).symm
  rw [hF] at hmap
  rw [hF, ← hmap]
  refine lintegral_image_prod_Ico_of_invariant e ν
    (h := fun g => ‖φ g‖ₑ ^ 2) (k := fun x => ‖φ (x : GA E a)‖ₑ ^ 2)
    (hc.enorm.measurable.pow_const 2) (fun x t => ?_) _
  simp only [he, hinv]

end GlobalTheory.CompanionTheory.CuspTransfer
end

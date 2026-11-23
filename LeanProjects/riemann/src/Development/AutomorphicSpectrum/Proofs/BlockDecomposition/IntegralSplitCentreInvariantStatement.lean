import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSplitCentreInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure] (c : ENNReal), Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ φ : GA E a → ℂ, Continuous φ → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∫⁻ g in ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)), ‖φ g‖ₑ ^ 2 ∂(c • μ) = ∫⁻ x in RightCosetSpace.fundamentalDomain (rationalGLOne E a), ‖φ (x : GA E a)‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq | exact GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq <;> assumption)

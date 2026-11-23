import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_haar_scaling_norm : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  first | exact @GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | exact GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | (intros; apply GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar <;> assumption)

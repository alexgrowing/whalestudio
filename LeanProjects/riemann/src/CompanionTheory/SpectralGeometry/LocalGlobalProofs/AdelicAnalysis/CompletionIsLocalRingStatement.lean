import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_is_local_ring : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | exact GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv <;> assumption)

import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_local_measures : ∀ (F : Type) [Field F] [NumberField F], (∃ laminf : Measure (Ainf F), IsStdInf laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ lam : Measure (Fv F v), IsStdV v lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StdEx.exists_std | exact GlobalTheory.CompanionTheory.SW.StdEx.exists_std | (intros; apply GlobalTheory.CompanionTheory.SW.StdEx.exists_std <;> assumption)

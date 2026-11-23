import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetMatrixPairIntegralOutside
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_matrixPair_integral_outside : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (M N : Matrix κ κ (Af F)), ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ i j, evalV F v (M i j) ∈ v.adicCompletionIntegers F ∧ evalV F v (N i j) ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.matrixPair_integral_cofinite | exact GlobalTheory.matrixPair_integral_cofinite | (intros; apply GlobalTheory.matrixPair_integral_cofinite <;> assumption)

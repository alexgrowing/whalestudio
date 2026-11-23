import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIntegersTopology
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIntegers_topology : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), CompactSpace (OPart F S) ∧ SecondCountableTopology (OPart F S) ∧ T2Space (OPart F S) := by
  first | exact @GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 | exact GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 | (intros; apply GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 <;> assumption)

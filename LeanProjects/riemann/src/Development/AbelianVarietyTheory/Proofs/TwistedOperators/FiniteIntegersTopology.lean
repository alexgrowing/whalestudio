import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem finiteIntegers_compact_secondCountable_t2 : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), CompactSpace (OPart F S) ∧ SecondCountableTopology (OPart F S) ∧ T2Space (OPart F S) := by
  intro F _ _ S
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, CompactSpace (v.1.adicCompletionIntegers F) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    fun v => secondCountable_of_proper
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, SecondCountableTopology (v.1.adicCompletionIntegers F) :=
    fun v => TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.ModuLR

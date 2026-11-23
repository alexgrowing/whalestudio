import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem matrixPair_integral_cofinite (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (M N : Matrix κ κ (Af F)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ i j,
      evalV F v (M i j) ∈ v.adicCompletionIntegers F ∧
      evalV F v (N i j) ∈ v.adicCompletionIntegers F := by
  have hM : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (M p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (M p.1 p.2).2
  have hN : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (N p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (N p.1 p.2).2
  have h := hM.and hN
  rw [Filter.eventually_cofinite] at h
  refine ⟨h.toFinset, fun v hv i j => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1 (i, j), hv.2 (i, j)⟩

end GlobalTheory

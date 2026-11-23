import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaledIntegralFiniteAdelePoints_subset_nhds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  first | exact @GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds | exact GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds | (intros; apply GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds <;> assumption)

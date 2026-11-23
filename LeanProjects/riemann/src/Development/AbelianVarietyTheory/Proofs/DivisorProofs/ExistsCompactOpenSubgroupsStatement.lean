import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroups
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_open_subgroups : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (V : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    V ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (N v : Set (v.adicCompletion F))) ∧ (∀ v, IsCompact (N v : Set (v.adicCompletion F))) ∧
      (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ⊆ V := by
  first | exact @GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset | exact GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset | (intros; apply GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset <;> assumption)

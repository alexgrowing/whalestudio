import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PIsotropicRank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem UnitaryIsotropicRank.proof : UnitaryIsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A I hI ρ v hv
  obtain ⟨-, hvI, hli, -⟩ := hv
  have hliE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).mp hli
  have hS : ∀ x ∈ (I : Set (Fin N → Em)), ∀ y ∈ (I : Set (Fin N → Em)), hermForm Em A.H x y = 0 := hI
  have hle : Submodule.span Em (Set.range v) ≤ Submodule.span Em (I : Set (Fin N → Em)) :=
    Submodule.span_mono (Set.range_subset_iff.2 hvI)
  calc ρ = Module.finrank Em (Submodule.span Em (Set.range v)) := by
        rw [finrank_span_eq_card hliE, Fintype.card_fin]
    _ ≤ Module.finrank Em (Submodule.span Em (I : Set (Fin N → Em))) := Submodule.finrank_mono hle
    _ ≤ N - j := IsotropicRank.proof Em Ψ N j A (I : Set (Fin N → Em)) hS

end GroundTheory.Heights₂.Heights.NineStatements

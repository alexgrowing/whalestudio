import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroup
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup : ∀ (K V : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) → ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  first | exact @GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | exact GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | (intros; apply GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacter
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_representation_character : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)

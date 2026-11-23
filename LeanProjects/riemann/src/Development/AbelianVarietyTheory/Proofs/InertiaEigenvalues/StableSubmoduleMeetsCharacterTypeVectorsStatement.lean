import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_submodule_meets_character_type_vectors : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  first | exact @GlobalTheory.MeetsTypeVec.meets | exact GlobalTheory.MeetsTypeVec.meets | (intros; apply GlobalTheory.MeetsTypeVec.meets <;> assumption)

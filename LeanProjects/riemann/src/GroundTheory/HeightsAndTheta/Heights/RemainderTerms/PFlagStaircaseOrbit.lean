import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

theorem FlagStaircaseOrbit.bijective_of_injective {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro i j h
  exact hinj (congrArg Fin.val h)

theorem FlagStaircaseOrbit.proof : FlagStaircaseOrbit.Statement := by
  intro f N α β hα hβ iα iβ
  let A : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective α τ (hα τ) (iα τ))
  let B : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective β τ (hβ τ) (iβ τ))
  refine ⟨fun τ => (B τ).trans (A τ).symm, fun τ i => ?_⟩
  have h : A τ ((A τ).symm (B τ i)) = B τ i := Equiv.apply_symm_apply _ _
  have h' := congrArg Fin.val h
  exact h'

end

end GroundTheory.Heights₂.Heights.RestTerms

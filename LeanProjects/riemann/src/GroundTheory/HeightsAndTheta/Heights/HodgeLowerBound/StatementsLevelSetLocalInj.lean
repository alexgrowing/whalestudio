import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def LevelSetLocalInj.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (R : Type) [Fintype R] (f : R → MvPolynomial J ℂ) (w₀ : J → ℂ),
    LinearIndependent ℂ (fun i => fun j => eval w₀ (pderiv j (f i))) →
    ∀ m : ℕ, m + Fintype.card R = Fintype.card J →
      ∃ U : Set (J → ℂ), IsOpen U ∧ w₀ ∈ U ∧ ∃ π : (J → ℂ) →L[ℂ] (Fin m → ℂ),
        Set.InjOn π (U ∩ {w | ∀ i, eval w (f i) = eval w₀ (f i)})

end GroundTheory.Heights₂.Heights.LowerBoundFree

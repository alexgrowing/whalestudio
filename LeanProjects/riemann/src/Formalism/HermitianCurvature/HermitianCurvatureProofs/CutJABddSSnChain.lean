import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ChainBd : Prop :=
  ∀ (k r : ℕ) (V E' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Ψ : V → E'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
    ∀ (F : Mat k r → V) (U K : Set (Mat k r)), IsOpen U → CkOn ⊤ (U ∩ GV k r) F → K ⊆ U → K ⊆ GV k r →
    ∀ Bg : ℝ, 0 ≤ Bg →
    (∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v F g‖ ≤ C * gN g ^ (Bg * m)) →
    ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v (fun g => Ψ (F g)) g‖ ≤ C * gN g ^ (Bg * m)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn

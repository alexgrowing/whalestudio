import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

def RuleOfEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (Φ : Q.Mx k r → E) (g : Q.Mx k r), inWb k r z' →
    (∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g) →
    ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g

def AdjoinNL : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r) (z : Fin (2 * r + k + 1) → ℂ)
    (Dm : Set (Q.Mx k r)) (hD : IsOpen Dm),
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm) →
    ∀ x ∈ Algebra.adjoin ℂ (Set.range fun pq : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) =>
        (PBG.E0 (E := E) hD pq.1 pq.2 : Module.End ℂ (Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E))),
    ∀ v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E,
      (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        (v : Q.Mx k r → E) (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • (v : Q.Mx k r → E) g) →
      ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) (nL k r j hj a * g) =
          psi k r z cStd (nL k r j hj a) • ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) g

end Formalism.FourierDecayAlt.P.LevelPointCoordinates

import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Pp (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u', P.u'⟩

def Pq (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u, P.u⟩

def inLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ X *ᵥ z = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0

def SmVec {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (π : Mx k r → (Wp →L[ℂ] Wp)) : Set Wp :=
  {x | ∀ h ∈ UWset k r z, ∀ X : Mx k r, inLieW k r z X →
    DifferentiableAt ℝ (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) x) 0}

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

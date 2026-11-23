import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FinalG

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

def Xsp (k r : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def FixSub : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → FixSet k r z ⊆ Sset k r z

def SubFlag : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → Sset k r z ⊆ FlagStab k r z

def UnipN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z →
    ∀ g ∈ Sset k r z, ∀ p : ℕ, (g - 1) ^ p = 0 → g ∈ Nset k r

def NPerp : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ v : Fin (2 * r + k + 1) → ℂ,
    (∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0) → (g - 1) *ᵥ v ∈ Xsp k r

end PI.StabSplit

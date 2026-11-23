import Mathlib
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB

noncomputable section

namespace PI.WHw

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def StableClosedC : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N) (U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    U ≤ nablaSq ℂ N lam → (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) →
    RowDivClosed U

def FixedKilledC : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ f ∈ nablaSq ℂ N lam,
    (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
    ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k f = 0

def HWInClosedC : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ), M ≤ dualWeyl ℂ r n ν → RowDivClosed M → M ≠ ⊥ →
      hw ℂ hn ν ∈ M

def ClosedEqNablaC : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ), M ≤ dualWeyl ℂ r n ν → RowDivClosed M →
      hw ℂ hn ν ∈ M → M = dualWeyl ℂ r n ν

end PI.WHw

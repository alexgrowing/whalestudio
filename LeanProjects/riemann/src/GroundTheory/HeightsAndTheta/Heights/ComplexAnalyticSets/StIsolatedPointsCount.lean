import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def isolatedFibrePts {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (z : Fin m → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ (∀ i, eval x (Q i) = z i) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, (∀ i, eval x' (Q i) = z i) → x' = x}

def IsolatedPointsCount.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts J Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights

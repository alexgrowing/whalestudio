import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def leadForm (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent f.totalDegree f

def leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)))

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range X)

def linIdeal (A : Matrix (Fin d) (Fin n) ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (linPoly A))

def ConeAvoids (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ) : Prop :=
  originIdeal n ^ N ≤ leadIdeal J ⊔ linIdeal A

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.ComplexSets

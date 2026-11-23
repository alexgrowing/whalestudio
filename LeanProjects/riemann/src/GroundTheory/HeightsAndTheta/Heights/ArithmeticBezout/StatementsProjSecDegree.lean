import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights

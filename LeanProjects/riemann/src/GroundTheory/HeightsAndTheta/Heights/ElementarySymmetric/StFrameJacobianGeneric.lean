import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def frameDeriv {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (j : Fin n)
    (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ l, C (b j l) * pderiv l f

def frameJacobianDet {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  Matrix.det (Matrix.of fun k j : {j // j ∉ I} => frameDeriv b j (f k))

def FrameJacobianGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ),
        I₀.card = d ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ frameJacobianDet b I₀ f ∉ J ∧
          ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights

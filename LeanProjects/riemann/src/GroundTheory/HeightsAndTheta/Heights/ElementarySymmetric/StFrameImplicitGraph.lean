import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameImplicitGraph.Statement : Prop :=
  ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)),
    (∀ k, eval (fun i => z i) (f k) = 0) → eval (fun i => z i) (frameJacobianDet b I f) ≠ 0 →
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → z ∈ U →
      ∃ (Ω : Set (I → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n))) (g : (I → ℂ) → EuclideanSpace ℂ (Fin n)),
        IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I (g w) = w) ∧
          {x : EuclideanSpace ℂ (Fin n) | ∀ k, eval (fun i => x i) (f k) = 0} ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights

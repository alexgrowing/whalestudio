import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def VarietyTangentGraphDense.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ ε : ℝ, 0 < ε →
      ∃ (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
        (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
        I₀.card = d ∧ IsOpen Ω ∧ IsOpen V ∧ w₀ ∈ Ω ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ zeroSetEuc J ∩ V = g '' Ω ∧
          (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) ∧ dist (g w₀) z < ε

def VarietyTangentGraphDense.lineMap :
    (↥(Finset.univ : Finset (Fin 1)) → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 1 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (⟨j, Finset.mem_univ j⟩ : (Finset.univ : Finset (Fin 1))))

end

end GroundTheory.Heights₂.Heights

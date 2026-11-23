import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def deepMap {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  vecCons (eval y P) fun i => s y (I i)

def deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : ℂ :=
  LinearMap.det ((fderiv ℂ (deepMap P s I) y : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))

def TubeDeepRankOne.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (U : Set (Fin (d + 1) → ℂ)) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ),
    IsOpen U → y ∈ U → DifferentiableOn ℂ s U → (∀ y' ∈ U, A *ᵥ s y' = y') → eval y P ≠ 0 →
      ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y =
        (2 / Real.pi) ^ (d + 1) * ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 / ‖eval y P‖ ^ 2

end

end GroundTheory.Heights₂.Heights

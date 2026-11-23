import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def logDistSq {n : ℕ} (x : Fin n → ℂ) (z : Fin n → ℂ) : ℝ :=
  Real.log (euclPot (z - x))

def RegLogDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → z ≠ x → IsSheetAt J A z s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => logDistSq x : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s)
        (A *ᵥ z)

end

end GroundTheory.Heights₂.Heights

import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ComplexSets

noncomputable section

def MaDensLogPow.Statement : Prop :=
  ∀ (e : ℕ) (φ₀ p : (Fin (e + 1 + 1) → ℂ) → ℝ) (y : Fin (e + 1 + 1) → ℂ),
    ContDiffAt ℝ 2 p y → 0 < p y →
      maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p) y =
        maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => p) y / p y ^ (e + 1) -
          ((e + 1 : ℕ) : ℝ) * gradDens (Fin.cons φ₀ fun _ : Fin e => p) p p y / p y ^ (e + 2)

end

end GroundTheory.Heights₂.Heights

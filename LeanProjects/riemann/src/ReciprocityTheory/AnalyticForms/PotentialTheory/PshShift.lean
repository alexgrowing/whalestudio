import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LeviCompStatement : Prop :=
  ∀ {e e' : ℕ} (φ : (Fin e' → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin e' → ℂ)) (z w : Fin e → ℂ),
    AnalyticAt ℂ τ z → ContDiffAt ℝ 2 φ (τ z) →
      levi (φ ∘ τ) z w = levi φ (τ z) (fderiv ℂ τ z w)

theorem pshShift : PshShiftStatement := plurisubharmonicShift_proof

end

end ReciprocityTheory.AnForm.M

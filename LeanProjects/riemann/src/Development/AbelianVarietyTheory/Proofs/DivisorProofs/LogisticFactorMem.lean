import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst

noncomputable section

namespace GlobalTheory.InterpCurv

def logisticFactor (κ L u : ℝ) : ℝ := 1 / (1 + Real.exp (κ * (u - L)))

def weightProfile (χ : ℝ → ℝ) (κ L t u : ℝ) : ℝ :=
  t * (χ (u / L) / (1 + Real.exp (κ * (u - L))))

theorem weightProfile_eq (χ : ℝ → ℝ) (κ L t u : ℝ) :
    weightProfile χ κ L t u = t * (χ (u / L) * logisticFactor κ L u) := by
  rw [weightProfile, logisticFactor, mul_one_div]

theorem logisticFactor_mem (κ L u : ℝ) :
    0 < logisticFactor κ L u ∧ logisticFactor κ L u < 1 := by
  have h := Real.exp_pos (κ * (u - L))
  refine ⟨by unfold logisticFactor; positivity, ?_⟩
  rw [logisticFactor, div_lt_one (by positivity)]
  linarith

end GlobalTheory.InterpCurv

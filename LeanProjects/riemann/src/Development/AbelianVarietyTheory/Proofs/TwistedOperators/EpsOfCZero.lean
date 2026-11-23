import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Chamber

def eLC {k : ℕ} (l m H : A0 k) : ℂ := Complex.exp (Complex.I * (⟪l, H⟫_ℝ : ℝ) - (⟪m, H⟫_ℝ : ℝ))

def epsOfC {k : ℕ} (s : Finset (SV k)) (b : SV k → A0 k) (l m : A0 k) : ℂ :=
  (√(Matrix.gram ℝ fun u : s => b u).det : ℝ) * ∏ u ∈ s, (Complex.I * (⟪l, b u⟫_ℝ : ℝ) - (⟪m, b u⟫_ℝ : ℝ))⁻¹

theorem eLC_zero {k : ℕ} (l H : A0 k) : eLC l 0 H = eL l H := by simp [eLC, eL]

theorem epsOfC_zero {k : ℕ} (s : Finset (SV k)) (b : SV k → A0 k) (l : A0 k) : epsOfC s b l 0 = epsOf s b l := by
  simp [epsOfC, epsOf]

end GlobalTheory.Chamber

end

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

noncomputable section

open MeasureTheory Matrix Ad3.K.LC

namespace GlobalTheory.CompanionTheory.PerUC

def rr (h : M22) : ℝ := ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2

def yb (h : M22) : ℝ := GlobalTheory.CompanionTheory.MajC.dt h ^ 2 / rr h ^ 2

def gx (σ : ℝ) (N : ℕ) (h : M22) : ℝ :=
  (GlobalTheory.CompanionTheory.MajC.dt h ^ 3)⁻¹ * (yb h ^ ((1 : ℝ) / 2) * (1 + |Real.log (yb h)|) / (1 + yb h) ^ N) *
    (GlobalTheory.CompanionTheory.MajC.col h / GlobalTheory.CompanionTheory.MajC.dt h) ^ (2 * σ - 2) / (1 + ‖h‖) ^ N

def ga (σ : ℝ) (m : ℕ) (h : M22) : ℝ :=
  if ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0 then
    ‖h 0 0‖ ^ (-2 - 2 * σ) * ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ *
      GlobalTheory.CompanionTheory.MajC.kern (1 - σ) ‖h 0 0‖ (h 1 1 - h 1 0 / h 0 0 * h 0 1)
  else 0

end GlobalTheory.CompanionTheory.PerUC

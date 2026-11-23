import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticDerivBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logistic_deriv_bounds : ∀ (κ t σ ρ : ℝ), 0 < κ → 0 ≤ t → t ≤ 1 → 0 < σ → σ < 1 → 0 ≤ ρ → |t * (-κ * σ * (1 - σ))| + |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))| ≤ (κ + κ ^ 2) * (1 - t * σ) ∧ |t * (-κ * σ * (1 - σ))| + |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))| ≤ (κ + κ ^ 2) * (t * σ + ρ * (1 - t * σ)) ∧ (t * (-κ * σ * (1 - σ))) ^ 2 ≤ (κ + κ ^ 2) * (t * σ) * (t * σ + ρ * (1 - t * σ)) := by
  first | exact @GlobalTheory.InterpCurv.scaled_logistic_deriv_bounds | exact GlobalTheory.InterpCurv.scaled_logistic_deriv_bounds | (intros; apply GlobalTheory.InterpCurv.scaled_logistic_deriv_bounds <;> assumption)

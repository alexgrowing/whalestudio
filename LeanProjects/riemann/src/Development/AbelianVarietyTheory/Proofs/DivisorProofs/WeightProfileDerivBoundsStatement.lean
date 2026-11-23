import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightProfileDerivBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_profile_deriv_bounds : ∀ (κ M L t c c1 c2 σ ρ : ℝ), 0 < κ → 0 ≤ M → 1 / 2 ≤ L → 0 ≤ t → t ≤ 1 → 0 ≤ c → c ≤ 1 → |c1| ≤ M → |c2| ≤ M → c1 ^ 2 ≤ M * c → 0 < σ → σ ≤ 1 / 2 → σ ≤ ρ → |t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))| + |t * (c2 / L ^ 2 * σ + 2 * (c1 / L) * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)))| ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (1 - t * (c * σ)) ∧ |t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))| + |t * (c2 / L ^ 2 * σ + 2 * (c1 / L) * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)))| ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (t * (c * σ) + ρ * (1 - t * (c * σ))) ∧ (t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))) ^ 2 ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (t * (c * σ)) * (t * (c * σ) + ρ * (1 - t * (c * σ))) := by
  first | exact @GlobalTheory.profile_deriv_bounds_of_le_half | exact GlobalTheory.profile_deriv_bounds_of_le_half | (intros; apply GlobalTheory.profile_deriv_bounds_of_le_half <;> assumption)

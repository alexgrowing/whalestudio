import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticParameterBoundsOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_parameter_bounds_of_density : ∀ (K₁ A N f f1 f2 ρ a l : ℝ), 0 ≤ K₁ → 0 ≤ A → 0 ≤ N → 0 ≤ f → f < 1 → 0 ≤ ρ → 0 ≤ a → a ^ 2 ≤ A * N ^ 2 → |l| ≤ A * N ^ 2 → |f1| + |f2| ≤ K₁ * (1 - f) → |f1| + |f2| ≤ K₁ * (f + ρ * (1 - f)) → f1 ^ 2 ≤ K₁ * f * (f + ρ * (1 - f)) → |f1| * a ≤ K₁ * (A + √A + 1) * (1 - f) * N ∧ (|f1| * a) ^ 2 ≤ K₁ * (A + √A + 1) * N ^ 2 * f * (f + ρ * (1 - f)) ∧ |f1 * l + f2 * a ^ 2| ≤ K₁ * (A + √A + 1) * N ^ 2 * (f + ρ * (1 - f)) ∧ |f1 * l + f2 * a ^ 2| ≤ K₁ * (A + √A + 1) * N ^ 2 * (1 - f) := by
  first | exact @GlobalTheory.weight_bound_algebra | exact GlobalTheory.weight_bound_algebra | (intros; apply GlobalTheory.weight_bound_algebra <;> assumption)

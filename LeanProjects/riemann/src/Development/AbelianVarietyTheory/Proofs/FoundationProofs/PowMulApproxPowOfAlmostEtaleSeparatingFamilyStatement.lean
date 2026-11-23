import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  first | exact @GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | exact GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | (intros; apply GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep <;> assumption)

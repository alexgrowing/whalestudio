import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGenerator
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_improved_approx_kummer_generator : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 → (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F → v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤ max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  first | exact @GlobalTheory.AlmostEt.exists_approxRoot_step | exact GlobalTheory.AlmostEt.exists_approxRoot_step | (intros; apply GlobalTheory.AlmostEt.exists_approxRoot_step <;> assumption)

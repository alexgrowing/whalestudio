import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_tower_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  first | exact @GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | exact GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | (intros; apply GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one <;> assumption)

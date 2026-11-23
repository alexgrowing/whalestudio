import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧ ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  first | exact @GlobalTheory.coneCoord_le_pow_of_prod_eq_one | exact GlobalTheory.coneCoord_le_pow_of_prod_eq_one | (intros; apply GlobalTheory.coneCoord_le_pow_of_prod_eq_one <;> assumption)

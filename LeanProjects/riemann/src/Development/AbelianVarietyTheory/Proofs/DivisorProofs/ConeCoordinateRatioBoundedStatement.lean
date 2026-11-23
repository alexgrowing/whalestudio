import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBounded
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_coordinate_ratio_bounded : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  first | exact @GlobalTheory.cone_ratio_bounded | exact GlobalTheory.cone_ratio_bounded | (intros; apply GlobalTheory.cone_ratio_bounded <;> assumption)

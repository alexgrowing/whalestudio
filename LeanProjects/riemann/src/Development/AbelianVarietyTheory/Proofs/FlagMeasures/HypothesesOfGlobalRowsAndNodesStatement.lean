import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodes
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypotheses_of_global_rows_and_nodes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Glob0 D x eps CD Cg → Nodes D x eps → (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) → StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  first | exact @GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | exact GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | (intros; apply GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds <;> assumption)

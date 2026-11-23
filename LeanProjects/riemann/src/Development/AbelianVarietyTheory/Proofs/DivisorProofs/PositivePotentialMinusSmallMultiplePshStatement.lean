import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialMinusSmallMultiplePsh
import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_potential_minus_small_multiple_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (P Om : ReciprocityTheory.AnForm.M.LocPot X), ReciprocityTheory.AnForm.M.IsPotential A P → ReciprocityTheory.AnForm.M.IsPosPot A P → ReciprocityTheory.AnForm.M.IsPotential A Om → ∃ k : ℝ, 0 < k ∧ ReciprocityTheory.AnForm.M.IsPsh A (P + Om.rsmul (-k)) := by
  first | exact @GlobalTheory.PosDom.exists_pos_sub_isPsh | exact GlobalTheory.PosDom.exists_pos_sub_isPsh | (intros; apply GlobalTheory.PosDom.exists_pos_sub_isPsh <;> assumption)

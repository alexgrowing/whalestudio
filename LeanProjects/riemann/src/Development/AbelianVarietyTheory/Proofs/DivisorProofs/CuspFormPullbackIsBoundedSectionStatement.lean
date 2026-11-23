import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  first | exact @GlobalTheory.PullBdd.pull_isBddSec | exact GlobalTheory.PullBdd.pull_isBddSec | (intros; apply GlobalTheory.PullBdd.pull_isBddSec <;> assumption)

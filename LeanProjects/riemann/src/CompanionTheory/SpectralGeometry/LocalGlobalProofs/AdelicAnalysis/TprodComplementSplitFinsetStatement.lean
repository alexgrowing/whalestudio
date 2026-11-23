import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
import Mathlib
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_complement_split_finset : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | exact GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | (intros; apply GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut <;> assumption)

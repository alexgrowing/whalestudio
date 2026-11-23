import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTopFinrankOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_top_finrank_one : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  first | exact @GlobalTheory.topWedge_line_and_nonzero | exact GlobalTheory.topWedge_line_and_nonzero | (intros; apply GlobalTheory.topWedge_line_and_nonzero <;> assumption)

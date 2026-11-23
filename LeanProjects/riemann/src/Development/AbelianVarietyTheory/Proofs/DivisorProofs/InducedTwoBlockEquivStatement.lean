import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedTwoBlockEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_two_block_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), ∃ e : GlobalTheory.KSplit.indSp a a' α β ≃ₗ[ℂ] IndAA k a a' ![α, β], ∀ f x, (e f).1.1 x = (f : GL (Fin (a + a')) k → ℂ) x := by
  first | exact @GlobalTheory.IndEq.indSp_equiv_indAA | exact GlobalTheory.IndEq.indSp_equiv_indAA | (intros; apply GlobalTheory.IndEq.indSp_equiv_indAA <;> assumption)

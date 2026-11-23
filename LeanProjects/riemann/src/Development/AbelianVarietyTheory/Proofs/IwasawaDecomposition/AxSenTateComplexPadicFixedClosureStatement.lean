import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]), (∀ g ∈ H, Per.σC g x = x) → x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  first | exact @GlobalTheory.MemLoc.ax_sen_tate | exact GlobalTheory.MemLoc.ax_sen_tate | (intros; apply GlobalTheory.MemLoc.ax_sen_tate <;> assumption)

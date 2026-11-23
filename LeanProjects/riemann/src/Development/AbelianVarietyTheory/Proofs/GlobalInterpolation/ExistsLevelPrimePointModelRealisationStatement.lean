import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPrimePointModel_realisation : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T), ∃ M : PtModel B.ch i, Nonempty (B.Real i sp M) := by
  first | exact @GlobalTheory.LvT.Built.RealM.exists_real | exact GlobalTheory.LvT.Built.RealM.exists_real | (intros; apply GlobalTheory.LvT.Built.RealM.exists_real <;> assumption)

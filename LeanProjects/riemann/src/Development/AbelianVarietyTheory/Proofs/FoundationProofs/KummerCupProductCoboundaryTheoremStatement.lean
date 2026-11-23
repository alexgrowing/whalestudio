import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCupProduct_coboundary_theorem : GlobalTheory.NeedB.ThmA := by
  first | exact @GlobalTheory.KummerCob.thmA | exact GlobalTheory.KummerCob.thmA | (intros; apply GlobalTheory.KummerCob.thmA <;> assumption)

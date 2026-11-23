import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryHPAAtParameters
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entry_hPA_at_parameters : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints := by
  first | exact @GlobalTheory.Fc.RL.PrimAt.at_linked | exact GlobalTheory.Fc.RL.PrimAt.at_linked | (intros; apply GlobalTheory.Fc.RL.PrimAt.at_linked <;> assumption)

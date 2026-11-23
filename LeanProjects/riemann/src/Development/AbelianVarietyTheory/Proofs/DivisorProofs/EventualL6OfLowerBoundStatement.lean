import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBound
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_L6_of_lower_bound : GlobalTheory.BigTop.LamLow → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvWC (fun _ => True) L6 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar | exact GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar | (intros; apply GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar <;> assumption)

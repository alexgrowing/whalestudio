import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualOntoOfMorePoints
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_onto_of_more_points : GlobalTheory.BigOn.OntoX → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) ON 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.onto_at_chosen | exact GlobalTheory.Fc.Ind.onto_at_chosen | (intros; apply GlobalTheory.Fc.Ind.onto_at_chosen <;> assumption)

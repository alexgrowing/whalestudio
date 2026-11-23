import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTiesStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

theorem onto_at_chosen : GlobalTheory.BigOn.OntoX → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ →
    EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) ON 𝒜 σ :=
  fun h 𝒜 σ hD hR hM =>
    GlobalTheory.T.eventual_points_of_row_ties (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigOn.More p)
      (fun C CH _ _ _ p => (p.S false).ON (p.N C CH)) h 𝒜 σ hD hR hM

end GlobalTheory.Fc.Ind

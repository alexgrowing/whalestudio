import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTiesStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

theorem eventual_L3_of_covolume : GlobalTheory.CovTop.CovolX → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ →
    EvW (fun D O _ _ => GlobalTheory.CovTop.RecTied D O.L) 𝒜 σ → EvWC (fun _ => True) L3 𝒜 σ := by
  intro h 𝒜 σ hd hr ht
  refine GlobalTheory.T.eventual_points_of_row_ties (fun _ => True) (fun D O _ _ => GlobalTheory.CovTop.RecTied D O.L)
    (fun C CH _ _ _ p => (p.S false).L3 (p.N C CH)) ?_ 𝒜 σ hd hr ht
  exact Closed.imp h fun _ _ _ ⟨C0, h0, a, h⟩ _ => ⟨C0, h0, a, fun x hx hle ι p hp hg => h x hx hle ι p ⟨hp, hg⟩⟩

end GlobalTheory.Fc.Ind

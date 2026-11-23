import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTiesStatement
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

theorem eventual_L6_of_lower_scalar : GlobalTheory.BigTop.LamLow → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvWC (fun _ => True) L6 𝒜 σ := by
  intro h 𝒜 σ hd hr
  have hG : EvW (onPt fun _ _ _ _ => True) 𝒜 σ :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ _ => ⟨0, fun _ _ _ _ => trivial⟩
  have key := GlobalTheory.T.eventual_points_of_row_ties (fun _ => True) (fun _ _ _ _ => True) lowScalarPt ?_ 𝒜 σ hd hr hG
  · exact key
  · obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    refine ⟨K, fun Fm CH hc hL _ => ⟨0, le_rfl, ?_⟩⟩
    obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
    exact ⟨x0, fun x hx hle i p hp _ C _ => hx0 x hx hle i p hp C⟩

end GlobalTheory.Fc.Ind

end

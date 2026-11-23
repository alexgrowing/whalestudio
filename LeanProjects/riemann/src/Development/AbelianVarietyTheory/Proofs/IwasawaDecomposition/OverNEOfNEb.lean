import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.Mem.AtPtTransport

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem overNE_of_NEb {N : NExt hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) :
    GlobalTheory.NRows.AtPt.OverNE N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩

theorem atMem_at_wit : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : LayP hL, AtMem hL p → RL.At (prmR N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (prmR N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (WPt.core (p := prmR N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, AtMem hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      RL.At (prmR N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := overNE_of_NEb hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (GlobalTheory.NRows.AtPt.largeBasePropertyG_memberProperty hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := GlobalTheory.NRows.AtPt.exists_wit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact GlobalTheory.NRows.AtPt.lg1_entryPred_of_atMem_witMv hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _

end GlobalTheory.Mem.AtPtTransport

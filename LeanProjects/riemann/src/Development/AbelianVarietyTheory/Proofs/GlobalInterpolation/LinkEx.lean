import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ClosedRankTiesFC2S
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Top.link_ex : ∀ (𝒜 : FamClass)
    (cT : ℝ → ℝ → ℝ)
    (hEx : MinkDiv → DesignChoices (WithTw 𝒜) 3 cT)
    (sel : Formalism.L2.TSel 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLit : LitThin), DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 := by
  intro 𝒜 cT hEx sel hduty hTu hn4 hLit
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Formalism.L2.LayerTwoFamilyClass Fm := fun Fm hc =>
    class_of_record_of_choice (sel Fm hc) (class_duties_of_choice (sel Fm hc) (hduty Fm hc))
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN 𝒜)) Fm → 𝒜 Fm := fun _ hc => hc.1.1.1
  have hProv : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ChosenProviso Fm 3 :=
    (hn4.and (Pk.Closed.sub Formalism.MainNotions.Ext.Lw.closed_rankTiesF_C2S fun Fm hc => (hRec Fm (hsub Fm hc)).c2s)).imp
      fun Fm _ _ h => Formalism.MainNotions.StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 hCe h.1 h.2
  have hE' : DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 :=
    designExists_of_choices (designChoices_upN (hEx minkowski_bound_rat)) hTu hProv
      (chosenThin_closed (WithTw (WithSm (WithChN 𝒜))) hLit)
  exact hE'

end

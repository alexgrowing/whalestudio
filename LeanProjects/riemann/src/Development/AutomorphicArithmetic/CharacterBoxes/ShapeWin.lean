import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.TopShape
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Development.AutomorphicArithmetic.CharacterBoxes.DesWin
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkEta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkGl
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallLevelRankEqClosedOfLevelProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkAlt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosedFamilyAdmissibleTwistLink
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelectionClosedOfWuDecay
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkBrest
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WireSel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 2000000 in

theorem UpperTheory.Top.shapeWin : GlobalTheory.GLq.Green → GlobalTheory.Fc.TopShape True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by
  intro hGreen 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB hTw hPA hLamP hDivG hDcPtG hTu hn4 hLit hVC hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR selJ jOn hMt rRows aPt0 aPtTw aPer0 aPerTw aP10 aAtG aC2 hServ nR nRest cIc hcI irrC zL tie hU hG la G hla hH hV
  have hgl := GlobalTheory.Top.link_gl 𝒜 hduty tie hU hG
  have bRest := GlobalTheory.Top.link_brest 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  have oneMap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, EvSel sel Fm (d3_a hc) ((OneMapOf selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩
  have hA2 := GlobalTheory.Top.closed_family_admissible_twist_link 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hC5 := GlobalTheory.Top.selection_closed_of_wu_decay 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have hBR : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm →
      Formalism.L2.DIV.BridgeRowsK Fm (RkOf sel selS selP selDH selC (selKOf selB) (selIOf selB) hPA Fm hc) 2 CH :=
    (bRest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (hMt Fm (d3_a hc))).and (rRows.and (oneMap.and (hCsz.and (hA2.and (aC2.and hC5))))))).imp
      fun Fm CH _ ⟨r, o, rr, om, cz, a, c, c5⟩ hc hT hD =>
        (r hc hT hD).toRows (fun hN => GlobalTheory.Top.wire_sel 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG Fm hc CH cz hD (rr hc) (om hc) (r hc hT hD).bu hN) o a (complement_two_of_items c) c5
  have hDIV := Formalism.L2.DIV.linkDIVt_closedK (D3 3 𝒜) 2 (RkOf sel selS selP selDH selC (selKOf selB) (selIOf selB) hPA) hBR
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm)) Fm →
      WithTw (WithSm (WithChN 𝒜)) Fm := fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := GlobalTheory.Top.link_ex (fun Fm => 𝒜 Fm ∧ G.cls la Fm) cT (fun hM => hEx hM la G hla hH) (fun Fm hc => sel Fm hc.1)
    (fun Fm hc => hduty Fm hc.1) (Pk.Closed.sub hTu hsub) (Pk.Closed.sub hn4 hsub) hLit
  exact UpperTheory.Top.topDesWin (WithChN 𝒜) (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm) (G.cls la) 2 3 2 0 hE
    (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV nRest (GlobalTheory.Top.link_eta 𝒜 sel hduty)
    (GlobalTheory.Top.Irr.link_irr hGreen 𝒜 sel cIc hcI irrC) (GlobalTheory.Top.smallLevelRankEq_closed_of_levelProjection_surjective 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL) hDIV hgl.1 (GlobalTheory.Top.link_g 𝒜 sel hduty)
    (GlobalTheory.Top.link_alt 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR) hgl.2

end

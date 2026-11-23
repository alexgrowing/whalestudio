import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs2Of
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntQ

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntQ

namespace BM

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem locDDQ (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (C : Choice X θ) (hLF : LocFactor C) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    ∃ (l : X.B.H (vOf X τ) → X.Vloc u (vOf X τ)) (a : ℂ),
      (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ),
        ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ),
          Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) (cS D) (piB X (C.Q τ) (C.Qi τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ)
            (C.muW u τ) (muNB D θ) x y = (innerSL ℂ (l y)).smulRight (l x)) ∧
      ∀ γ, X.Wloc u (vOf X τ) γ = a • l (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) := by
  obtain ⟨h, hHC, hDS', hgap, hok, hz, hT, hc, hty, hlow, hμG, hμW, hμN, hq, hWc, hWe, hWr, hne, hfin⟩ :=
    sideQ hRT hL2 hGp hG hLF (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ) u τ
  have hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ)
      (zB X (C.Qi τ) u τ) (cS D) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) (C.muW u τ) (muNB D θ)
      (muGB X (C.Q τ) (C.Qi τ) τ) (C.nuS u τ) :=
    ⟨hHC, hDS', hgap, hok, hlow, hz, hT, hc, hty, hμW, hμN, hμG, hq⟩
  obtain ⟨x0, hx0, y0, hy0, hbe⟩ := CompanionTheory.D.Upq.BesselFunctionalConstruction.bessel_nonvanishing_L2 CompanionTheory.Lime.BM.inputs Formalism.FourierDecayAlt.P.schur_hermitian D.R.k D.R.rS
    (epsSH D.R) (lamD D τ) h _ _ (v0Of C τ) _ _ (cS D) _ _ _ _ _ _ hSide _ hWc hWe hWr (pos_iff_ne_zero.mpr hne) hfin
  obtain ⟨l, hl, ⟨x1, hx1, hlx1⟩, hbel⟩ := CompanionTheory.Lime.BM.shape hI.2.2.2 CompanionTheory.Lime.BM.inputs D.R.k D.R.rS (epsSH D.R) (lamD D τ) h _ _
    (v0Of C τ) _ _ (cS D) _ _ _ _ _ _ hSide ⟨x0, hx0, y0, hy0, hbe⟩
  have hWB : WuBessel C := wuBesselOfLoc hRT hL2 hGp C hG
    Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds hLF (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  obtain ⟨B, hB, hWB'⟩ := hWB u τ
  have hDDs := Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hI.2.2.1 hHC hDS' hlow
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) (zB X (C.Qi τ) u τ)
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun _ => cS D)) (sigB X (C.Q τ) (C.Qi τ) τ)
      (piB X (C.Q τ) (C.Qi τ) u τ) B := by
    rw [psiGen_const']; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ B).1 hB
  have hl' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) (zB X (C.Qi τ) u τ)
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun _ => cS D)) (sigB X (C.Q τ) (C.Qi τ) τ)
      (piB X (C.Q τ) (C.Qi τ) u τ) l := by
    rw [psiGen_const']; exact hl
  obtain ⟨a, b, hab, hlin⟩ := hI.2.2.2 D.R.k D.R.rS (epsSH D.R) (lamD D τ) h _ (sigB X (C.Q τ) (C.Qi τ) τ)
    (zB X (C.Qi τ) u τ) (fun _ => cS D) (fun i => ((D.hcW u τ).u i : ℝ)) _ (piB X (C.Q τ) (C.Qi τ) u τ)
    hok.1 hgap hok.2.1 hHC hDS' hz hT
    (fun _ => hc) hty B l hB' hl'
  have ha : a ≠ 0 := by
    intro ha0
    have hb : b ≠ 0 := hab.resolve_left (fun h => h ha0)
    apply hlx1
    have := hlin x1 (hDDs x1 hx1)
    rw [ha0, zero_smul, zero_add] at this
    exact (smul_eq_zero.mp this).resolve_left hb
  refine ⟨l, -(b / a), fun x hx y hy => hbel x (hDDs x hx) y hy, fun γ => ?_⟩
  rw [hWB' γ]
  have hsm := hDDs _ (mem_DD C τ γ)
  have h0 := hlin _ hsm
  have e : B (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) =
      a⁻¹ • (a • B (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)))) := by
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [e, eq_neg_of_add_eq_zero_left h0, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end BM

end Formalism.L2.SG.RealObj.EnergyIntQ

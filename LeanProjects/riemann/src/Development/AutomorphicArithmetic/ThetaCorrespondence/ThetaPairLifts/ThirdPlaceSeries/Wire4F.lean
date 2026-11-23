import Formalism.LocalToGlobal.Wire4F
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GammaSizeOfParameters
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InpAtOf

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
theorem wire4F_alt [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) (hCabs : 1 ≤ Cabs)
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hD0 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      (Fm.D x i).what₂.D0 = ((selP Fm hc x hx h i).1.A3.A.fam.R (selP Fm hc x hx h i).1.A3.A.fam.μ0).dZ ((selP Fm hc x hx h i).1.A3.A.fam.lvl (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0)
        ((selP Fm hc x hx h i).1.Zs.Z (selP Fm hc x hx h i).1.A3.A.fam.μ0))
    (hPt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      RowsHoldDcPt3 (selP Fm hc x hx h i).1)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    :
    _root_.Formalism.L2.Top4.Wire4Alt sel selS selP selDH selC selK selI hPA (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt selI Fm hc x hx h i C CH)
      OneMapRow Cabs := by
  intro eps Fm hc CH hCsz hDG hRows hOne _hBu hN
  obtain ⟨Ce, x3, hCe⟩ := id hN
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max 0 (max (50 * c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct + 10)
      (60 * ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct))),
    max (max x1 x2) (max (max x3 x4)
      (x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))),
    fun x hx0 hx h i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hx3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, hd⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx h i
  have hok1 := (selC Fm (d3_a hc) x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm (d3_a hc) x hx h i).Rl (selI Fm (d3_a hc) x hx h i).F (selI Fm (d3_a hc) x hx h i).sEE (hkCan (selP Fm (d3_a hc) x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs = (selP Fm (d3_a hc) x hx h i).1.Zs := (selI Fm (d3_a hc) x hx h i).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.toIndefData (selP Fm (d3_a hc) x hx h i).1.S0 := (selI Fm (d3_a hc) x hx h i).s0
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := _root_.Formalism.L2.DIV.Cons.gamma_size_of_sizeData_alt (selP Fm (d3_a hc) x hx h i).2 (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0, Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 hS (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.tied.div.grp.card (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (selP Fm (d3_a hc) x hx h i).1.Ps (selP Fm (d3_a hc) x hx h i).1.ψs (selC Fm (d3_a hc) x hx h i).c.face (selC Fm (d3_a hc) x hx h i).Sp _ C CH Fm.Csz Ce
    (2 + 9 * max Cd 0) (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i)) hDGp hC hCsz hxL (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass)
  have e0 : c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct = c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct := by
    rw [eCc, eCY, eCt]
  exact _root_.Formalism.L2.RowDataTransport.ptK_of_real_alt ((sel Fm (d3_a hc)).2 x hx h i) ((_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) rfl
    (selP Fm (d3_a hc) x hx h i).2 ra.kap (hPt Fm (d3_a hc) x hx h i) (hR Fm (d3_a hc) x hx h i)
    (selS Fm (d3_a hc) x hx h i) (selI Fm (d3_a hc) x hx h i) hsep C CH hP ra.pass _ Cabs (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2
    (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H
    (_root_.Formalism.L2.RowDataTransport.inpAt_of_alt (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H Ce (hCe x hx3 i)
      (by rw [tw_heq hZs hS0]; exact hTw Fm (d3_a hc) x hx h i) (by rw [hZs]; exact hD0 Fm (d3_a hc) x hx h i)
      (lift_exponent_of_least (selP Fm (d3_a hc) x hx h i).1.A3.A hok1.ok2 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs)
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.μ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.Tw _ (fun _ _ _ => rfl))
      ⟨dg, hdg, hdvd, hA⟩ (fun NuC I hT hI u => hd hok1 hsep hP ra.pass lam0 _ _ Sw C1 H NuC I hT hI u))
    (Fm.nprimeDef x hx i) (fun u => Fm.h_eq x hx i u)
    (fixedScale_tied (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.ex x hx i).kap_def (Fm.ex x hx i).fdef (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (Equiv.refl _)
      (Fm.L x i).Nc Fm.Csz (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs C CH)
    (le_max_left _ _) (by rw [e0]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    (by rw [e0]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hCabs
    (Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x hx i).2.2.2.2.2.2.1)
end Formalism.L2.Top4Wire2
end
end

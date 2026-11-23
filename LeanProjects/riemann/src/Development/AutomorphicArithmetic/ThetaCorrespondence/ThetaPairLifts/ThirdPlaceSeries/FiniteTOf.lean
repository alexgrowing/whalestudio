import Formalism.LocalToGlobal.FiniteTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
def DefRowsFAlt (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) {eps : ℝ} (Fm : FamP eps)
    (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) [IsTotallyComplex (Fm.D x i).what₂.LL]
    (C CH : ℝ) : Prop :=
  ∀ (hok1 : (selP Fm hc x hx h i).1.A3.fam3.Ok3 1) (hsep : (selP Fm hc x hx h i).1.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH) (hI : PassIn3 (selI Fm hc x hx h i).Rl (faceT (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : NumFactsAt Fm x i (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 lam0 C0 ce Sw C1)
    (NuC : ∀ w, Submodule (𝓞 (Fm.D x i).what₂.LL) (Fin (((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs).a w) → (Fm.D x i).what₂.LL))
    (I : DivisionCompatibilityDataThreeSided (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 ((selC Fm hc x hx h i).c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs)),
    DivTied3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.toIndefData (Fm.ex x hx i).p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I (selP Fm hc x hx h i).1.I → ∀ u, RowsU (selC Fm hc x hx h i).c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _)
          (letterOf (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 u) ((Fm.D x i).mem u).A.T (Fm.L x i).Nc lam0 C0 ce Fm.Csz Sw C1 (H u)) (I.wU u) (Cons.nuOf (Fm.L x i) u (I.eNu u))
theorem finite_T_of_squareIntegrableColumns {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex}
    (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Finite P.T := by
  rw [K.tEq]
  exact ((Finset.finite_toSet K.TU).insert _).to_subtype
end Formalism.L2.Top4Wire2
end
end

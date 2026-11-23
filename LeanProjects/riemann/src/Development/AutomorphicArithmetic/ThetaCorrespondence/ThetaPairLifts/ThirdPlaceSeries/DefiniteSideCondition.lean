import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DRS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc
section Def
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
open GlobalTheory.EX GlobalTheory.EX.OB
abbrev qRealOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) :
    _root_.Formalism.IndefR.IndefiniteRealisation b.R b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c) b.S b.B.T.Q.c.F := b.B.Q
def DefiniteSideCondition : _root_.GlobalTheory.Fc.R1.DefiniteSideType := fun D O c b C CH =>
  ∀ (hok1 : b.P.A3.fam3.Ok3 1) (hsep : b.P.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) (_root_.GlobalTheory.Fc.qRealOfBundle b).sEE (hkCan b.P.A3) C CH) (hI : PassIn3 (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : ∀ u, (ofRecord D O.L b.DH.1.1 b.DH.1.2).NumFacts (letterOf D O.L b.DH.1.1 b.DH.1.2 u) O.L.Nc lam0 C0 ce c Sw C1)
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs).a w) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs)),
    DivTied3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I b.P.I → ∀ u, RowsU b.C.toS.c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord D O.L b.DH.1.1 b.DH.1.2) (Equiv.refl _)
          (letterOf D O.L b.DH.1.1 b.DH.1.2 u) (D.mem u).A.T O.L.Nc lam0 C0 ce c Sw C1 (H u)) (I.wU u) (Cons.nuOf O.L u (I.eNu u))
end Def
end GlobalTheory.Fc
end
end

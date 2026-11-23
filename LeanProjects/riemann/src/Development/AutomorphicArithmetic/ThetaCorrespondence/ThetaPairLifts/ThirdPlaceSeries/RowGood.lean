import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Fc.RL
open GlobalTheory.Fc
variable (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition)
def Row_tie_alt : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.HasCompatibility)
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 in
def RowLabelCondition : Prop := Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
  AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι)
def RowGoodnessCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D)
def RowGeometricCondition (CF : ℝ) : Prop := Row Q Lk (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∃ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt ∧
  GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF)
def RowMultiplicityCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b =>
  (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)
def RowKappaCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P)
def RowDefectCondition : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def LinkedAt (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (r : V4.Slot → LkT _root_.GlobalTheory.Fc.BundleCondition → Prop) : Prop :=
  Lg1 KPx (IsBuiltE p.s) (IsGoodE p.s) fun S => r S (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
theorem LinkedAt.of_row {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop} (h : Row (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) H) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L H :=
  ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, h.strengthen fun _ _ _ _ _ t => t.1⟩
end GlobalTheory.Fc.RL
end
end

import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Record
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
end Record
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
def AtPtsAlt (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => More p → Q Fm x hx i p
def ForallTwoRuns (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → Q Fm x hx i p r h
def ForallRecordObjects (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (c : OnConst),
    Obj p c → Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ c0 : ℝ, ∀ c : OnConst, c0 ≤ c.C → OnPage.ConstBad c →
    _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => More p → ∀ (r : TwoRuns p.T p.P.Gp) (O : Obj p c), RecAt p (Fm.parT x hx i) r O → Q Fm x hx i p c O
def TwoRunsStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun _ _ _ _ p => ∃ r : TwoRuns p.T p.P.Gp, RunsOk (fw2 p) r ∧ OwnPin r
def RationalityStatement' : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun _ _ _ _ p => TwistedRational (R2 p) (F2 p) fun _ => 1
def ExportedStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)
def MaximalityStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)
def GeometricStatement' : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ p _ O => LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O ∧ HasIndexBound O ∧
  ∀ C CH, LeafDepthGood ((R2 p).num (F2 p) C CH) O ∧ LeafDepthRam ((R2 p).num (F2 p) C CH) O ∧
    LeafDepth2 ((R2 p).num (F2 p) C CH) O ∧ LeafDepthLevel ((R2 p).num (F2 p) C CH) O
def TwistStatement' : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => HasTwistBound O
def ShareStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => LeafShareI O
def BadPlacesStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => LeafBadShare O
def ExponentStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ p _ O => ∀ C CH, HasExpBound ((R2 p).num (F2 p) C CH) O
def PageStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafPage O ∧ LeafSizes O ∧ LeafX O ∧ LeafBad O ∧
  LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O ∧ O.b = (Fm.L x i).sc.b ∧ 0 ≤ p.Z.E1u ∧
    ∀ C CH, ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH) O C
def SurjectiveOntoX : Prop := Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => More p → ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH)
section Checks
section Cell
end Cell
end Checks
end GlobalTheory.BigOn
end
end

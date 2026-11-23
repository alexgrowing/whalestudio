import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
abbrev LayPAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch), _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n → Prop
def MemberAtLayerPoint (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) →
    ColPin w → p K B f T w Z Wt p0 t nch n c
structure PinnedAtCharacterChoice {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : Prop where
  cf_eq : P.cf = cf
  C_eq : P.C = nch
  tp_eq : HEq P.tp tp
  rep_eq : HEq P.rep a.nt.rep
  M_eq : P.M = a.all.gal.mt
  lab : GlobalTheory.PendOf.LabAll D P.T
  green : GlobalTheory.PendOf.GreenLab P.ty.grp
  chiT : ChiTOk D P.cf
def ParameterStatement (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (Dof x) l.a.A.row
def ThetaDataExists (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ xd : ThData (Dof x), XdAll xd
def PointStatement (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D' ∧ SumRepresentations.Conclusion42 D' ∧ SumRepresentations.ConclusionZ D') ∧ D'.nd.EigSpan ∧ Rows.IsotInternal D'.what₂
end GlobalTheory.HeightCounting.Up
end
end

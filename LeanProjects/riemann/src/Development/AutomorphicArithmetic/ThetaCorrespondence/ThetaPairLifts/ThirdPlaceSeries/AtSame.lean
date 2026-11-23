import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Inner
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def AtSameAltAlt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) {D' : D7} {cf' : CharFrame D'}
    {C' : NChoice D'} {tp' : TupTied D' cf' C'} (a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D' cf' C' tp') : Prop :=
  HEq a'.all ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a.all) ∧ HEq a'.Pq a.Pq ∧ HEq (ratL a'.nt.L a'.nt.S) (ratL a.nt.L a.nt.S) ∧ HEq a'.nt.hL a.nt.hL ∧
    HEq a'.nt.rep a.nt.rep ∧ HEq a'.nt.eig a.nt.eig ∧ (_root_.GlobalTheory.LayerMove.InnerAlt a.nt → _root_.GlobalTheory.LayerMove.InnerAlt a'.nt)
section
end
end GlobalTheory.LayerMove
end
end

import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000
def mvCg_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE}
    (x : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) : _root_.GlobalTheory.HeightCounting.CGTrueT hL m.D (m.sideA_alt A).wdT :=
  @_root_.UpperTheory.One.M.New.cgMk _ _ _ s ((by with_unfolding_all exact (x.e :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgGood s x) :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgSurj x) :))) ((by with_unfolding_all exact (x.zero :))) ((by with_unfolding_all exact (x.loc :))) ((by with_unfolding_all exact (x.tw :))) ((by with_unfolding_all exact (x.inf :))) ((by with_unfolding_all exact (x.csd :)))
end UpperTheory.One.M
end
end

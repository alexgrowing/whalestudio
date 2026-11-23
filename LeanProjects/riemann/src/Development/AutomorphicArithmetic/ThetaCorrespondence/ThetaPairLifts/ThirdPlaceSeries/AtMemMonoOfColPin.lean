import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InputsJumpsAtMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
theorem atMem_mono_of_colPin {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {P : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
    (hP : EvLgG P) (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T, P K B f T → KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      Nonempty (RXs t) → ColPin w → p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp (EvG.inter hP h) fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T H.1 kp w Z Wt p0 t nch n xd c a b d (H.2 kp w Z Wt p0 t nch n xd c a b d)
end GlobalTheory.NRows.AtLayer
end
end

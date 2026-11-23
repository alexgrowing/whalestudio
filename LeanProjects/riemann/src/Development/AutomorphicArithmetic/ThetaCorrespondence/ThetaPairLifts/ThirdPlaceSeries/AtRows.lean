import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.LiftRef
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def ForallRowSideParameters (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (q : ∀ (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw →
      MtFam D → Prop) : Prop :=
  OverRows fun _ _ _ _ w Z _ _ _ _ Y => ∀ Rw (a : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw) (M : MtFam (w.st Z).toD7) tup Q,
    MtAd Y M → MtInput (w.st Z).toD7 M tup Q → q (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw a M
end GlobalTheory.LiftRef
end
end

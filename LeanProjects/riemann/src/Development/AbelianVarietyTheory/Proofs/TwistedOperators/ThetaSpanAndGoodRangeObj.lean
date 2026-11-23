import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.ThetaSpanObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem spanAtObj (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SizeOK D) (hL : R.toLevCh.Is A.μ0)
    (hF : R.IsFam) (hM : R.IsModels) (hT : R.IsThP) (i : Fin D.R.m) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i t :=
  GlobalTheory.AdSpan.spanAt R hP hsz hL hF hM hT i t

end GlobalTheory.ThetaSpanObj

end

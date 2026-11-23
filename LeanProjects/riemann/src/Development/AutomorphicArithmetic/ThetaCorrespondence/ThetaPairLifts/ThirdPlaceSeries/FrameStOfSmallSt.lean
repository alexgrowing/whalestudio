import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRangeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRangeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmallStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameOf
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
theorem inRange_and_alt {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (h2 : _root_.GlobalTheory.ExpTie.InRangeAlt Q2) :
    _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x hx i p j P W w => Q1 Fm x hx i p j P W w ∧ Q2 Fm x hx i p j P W w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 h2 ⊢
  refine Closed.imp (Closed.and h1 h2) fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and h.1 h.2
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR =>
    ⟨(hx0 x hx hle i p hp).1 hM j P W hD hN w hw hR, (hx0 x hx hle i p hp).2 hM j P W hD hN w hw hR⟩⟩
theorem inRange_of_dict_imp {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i)
      (j : Fin (Fm.D x i).R.m) (P : Par) (W : Wts (Fm.D x i).what₂.Tau) (w : HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL)),
      Dict (Fm.L x i) j P W → Q1 Fm x hx i p j P W w → Q2 Fm x hx i p j P W w) : _root_.GlobalTheory.ExpTie.InRangeAlt Q2 := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 ⊢
  refine Closed.imp h1 fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR => f Fm x hx i p j P W w hD (hx0 x hx hle i p hp hM j P W hD hN w hw hR)⟩
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem frameSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' := by
  intro hS
  have h := _root_.GlobalTheory.FrameOf.inRange_and_alt hS (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_halfAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_kapAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.chiAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.tame_at_of_small_at
    (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.permAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.commAt_of_smallAt_in_range _root_.GlobalTheory.T.readsAt_of_smallAt))))))
  refine _root_.GlobalTheory.FrameOf.inRange_of_dict_imp h fun Fm x hx i p j P W w hD hq => ?_
  obtain ⟨hs, hh, hk, hc, ht, hp, hcm, hr⟩ := hq
  exact frameAt_of p j P W w hD.Nr (hh hs) (hk hs) (hc hs) (ht hs) (hp hs) (hcm hs) (hr hs)
end GlobalTheory.FrameOf
end
end

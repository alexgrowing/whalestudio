import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHypothesisInHalfGeometry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option autoImplicit false
noncomputable section
theorem GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m),
    RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  intro hDec eps Fm x hx i p hR _hM t j h0
  have hJ : JEvExists p.T p.R.toRealDat p.κ p.v₀ :=
    GlobalTheory.ConjReading.jEvExists p.T p.R.toRealDat p.κ p.v₀ p.O h0.core.lev h0.core.models p.fw p.pins
  exact
    { jEvExists := hJ
      jEvBar := hR.jEvBar
      evInj := hR.evInj
      jUnif := GlobalTheory.ReadingSpan.jUnif hDec _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ h0.core.lev h0.core.models h0.tieIn
        hR.ties.pb hJ hR.jEvBar hR.evInj h0.size
      geoAct := hR.geoAct
      latFull := GlobalTheory.IntCuspLat.latFull_of_tie p.fw
      dimMatch := p.fw.dimMatch }
end
end

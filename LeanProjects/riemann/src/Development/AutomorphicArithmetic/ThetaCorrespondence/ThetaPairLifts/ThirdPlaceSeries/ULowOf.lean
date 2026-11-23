import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FromComp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem u_low_of_cover_hyps (h1 : _root_.GlobalTheory.CovTop.DeepGoodness) (h2 : _root_.GlobalTheory.CovTop.SizeCondition) (h3 : _root_.GlobalTheory.CovTop.CoverDegree) (h4 : _root_.GlobalTheory.CovTop.ShareCondition) (h5 : _root_.GlobalTheory.CovTop.HeightCondition) (h6 : _root_.GlobalTheory.CovTop.CoverHeightSum) (h7 : _root_.GlobalTheory.CovTop.SumBoundCondition) : _root_.GlobalTheory.CovTop.UniformLowerBound := by
  refine Closed.imp (Closed.and h1 (Closed.and h2 (Closed.and h3 (Closed.and h4 (Closed.and h5 (Closed.and h6 h7)))))) ?_
  rintro _ Fm _ _ ⟨⟨_, -, a1⟩, ⟨A, -, a2⟩, ⟨_, -, a3⟩, ⟨_, -, a4⟩, ⟨C1, hC1, a5⟩, ⟨C2, hC2, a6⟩, ⟨_, -, a7⟩⟩
  refine ⟨2 * (3 * C1 + C2 + 4), by positivity, ?_⟩
  obtain ⟨x0, h⟩ := a1.and (a2.and (a3.and (a4.and (a5.and (a6.and a7)))))
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h x hx hle ι p hp
  exact atPoint p i Y _ A C1 C2 hi (b1 i hi Y hY) (b2 i) (b3 i hi Y hY) (b4 i hi Y hY) (b5 i hi Y hY) (b6 i hi Y hY)
    (b7 i hi Y hY)
end GlobalTheory.CovTop.FromComp
end
end

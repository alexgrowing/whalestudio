import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.MeasUp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.CovTop.MeasUp
namespace GlobalTheory.CovTop.MeasUp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.MeasUp
namespace GlobalTheory.CovTop.MeasRd
theorem ratAt_upper_alt : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ =>
    ∃ K : ℝ, 0 ≤ K ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  intro hOM
  refine Closed.imp (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 2) _root_.GlobalTheory.CovTop.WtShape.wtN_z) fun Fm CH _ h => ?_
  obtain ⟨⟨A, -, hA⟩, ⟨C, -, hC⟩⟩ := h
  obtain ⟨x0, hx⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hA hC
  refine ⟨244, by norm_num, x0, fun x hx' hle ι p hp i => ?_⟩
  obtain ⟨h1, h2⟩ := hx x hx' hle ι p hp
  exact GlobalTheory.CovTop.MeasUp.ratAt_pos_le p i hOM (Fm.params x hx' ι) (h1 i) h2
end GlobalTheory.CovTop.MeasRd
end
end

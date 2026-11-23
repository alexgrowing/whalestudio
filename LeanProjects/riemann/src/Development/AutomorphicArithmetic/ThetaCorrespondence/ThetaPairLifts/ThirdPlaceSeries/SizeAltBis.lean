import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.SizeRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem size_of_alt (h1 : _root_.GlobalTheory.CovTop.HostNAlt 1) (h2 : _root_.GlobalTheory.CovTop.LiftWeightNumerator) : _root_.GlobalTheory.CovTop.SizeCondition := by
  refine (Closed.and h1 h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨A, hA, hH⟩, _, _, hW⟩ := h
  refine ⟨A + 2, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := hH.and hW
  exact ⟨x0, fun x hx hle ι p hp i => sizeAt_of p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩
theorem size_alt_bis : _root_.GlobalTheory.CovTop.SizeCondition := _root_.GlobalTheory.CovTop.SizeRows.size_of_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z
end GlobalTheory.CovTop.SizeRows
end
end

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.NumSizes
variable {D : D7} {L : SizeData₂ D}
variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem numPt_alt : _root_.GlobalTheory.RefSum.NumPtAlt := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨|Fm.Ct| + 20, by positivity,
    Real.exp (Real.exp 1), fun x hx hle ι p _ i _ => ?_⟩⟩⟩
  rw [← Fm.Ct_eq x ι]
  refine numAt p i (Fm.parT x hx ι) ?_
  rw [Fm.L_x x ι hx, Real.le_log_iff_exp_le, Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hle)]
  · exact hle
  · exact Real.log_pos ((Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans_le hle)
theorem numPt_of_size' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := fun _ => _root_.GlobalTheory.RefSum.NumSizes.numPt_alt
end GlobalTheory.RefSum.NumSizes
end
end

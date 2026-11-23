import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem sumPt_of_sizes_alt : _root_.GlobalTheory.RefSum.WtPtAlt → _root_.GlobalTheory.RefSum.NumPtAlt → _root_.GlobalTheory.RefSum.SumPtAlt := fun hw hn =>
  Closed.imp (Closed.and hw hn) fun _ _ _ ⟨⟨C₁, h1, e1⟩, C₂, h2, e2⟩ =>
    ⟨40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂, by positivity,
      (e1.and e2).imp fun _ h x hx hle ι p hp i hi u1 hu =>
        sumAt_of_sizes p i h1 h2 u1 ((h x hx hle ι p hp).1 i hi u1 hu) ((h x hx hle ι p hp).2 i hi)⟩
end GlobalTheory.RefSum
end
end

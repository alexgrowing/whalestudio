import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL3OfCovolumeTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem eventual_L3_of_covolume_alt : _root_.GlobalTheory.CovTop.CovolumeBoundOfX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ →
    EvW (fun D O _ _ => GlobalTheory.CovTop.RecTied D O.L) 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL3Bound 𝒜 σ := by
  intro h 𝒜 σ hd hr ht
  refine _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun _ => True) (fun D O _ _ => GlobalTheory.CovTop.RecTied D O.L)
    (fun C CH _ _ _ p => (p.S false).L3 (p.N C CH)) ?_ 𝒜 σ hd hr ht
  exact Closed.imp h fun _ _ _ ⟨C0, h0, a, h⟩ _ => ⟨C0, h0, a, fun x hx hle ι p hp hg => h x hx hle ι p ⟨hp, hg⟩⟩
end GlobalTheory.Fc.Ind
end

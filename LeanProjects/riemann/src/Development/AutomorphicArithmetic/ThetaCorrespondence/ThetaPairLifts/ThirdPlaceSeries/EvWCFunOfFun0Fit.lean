import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualFunctionGridLarge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_fun_of_fun0Fit_alt : ∀ Fld : GlobalTheory.BigTop.Fun.FldT, _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigTop.Fun.HasGrid @Fld b.pt CF) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 σ := by
  intro Fld h
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF 𝒜 σ hD hR hG => ?_⟩
  exact _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigTop.Fun.HasGrid @Fld p CF)
    (fun C CH _ _ _ p => (p.S false).FUN (p.N C CH))
    ((h CF hCF).imp fun Fm CH _ a hN =>
      ⟨0, le_rfl, _root_.GlobalTheory.BigTop.Fun.evPt_mono (a hN) fun _ _ _ _ _ b hg C _ => b hg C⟩) 𝒜 σ hD hR hG
end GlobalTheory.Fc.Ind
end

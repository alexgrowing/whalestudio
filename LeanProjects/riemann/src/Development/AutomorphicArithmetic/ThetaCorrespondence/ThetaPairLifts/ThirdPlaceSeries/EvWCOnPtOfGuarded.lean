import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_onPt_of_guarded_alt (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP)
    (h : Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p)
    (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜) (hd : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm)
    (hR : EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ) (hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint G) 𝒜 σ) : EvWC prem (fun C CH => _root_.GlobalTheory.Fc.Ind.conditionOnPoint (T C CH)) 𝒜 σ := by
  have h' : Closed (W3 𝒜) fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p := by
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties 𝒜 _ Fm hc (hd _ Fm (w3_a hc))) hL⟩
  refine Closed.imp (Closed.and h' (Closed.and hR hG)) ?_
  rintro eps Fm CH - ⟨h1, h2, h3⟩ hc hp
  obtain ⟨C0, hC0, a, ha⟩ := h1 hp
  obtain ⟨b, hb⟩ := h2 hc
  obtain ⟨c, hc'⟩ := h3 hc
  refine ⟨C0, hC0, fun C hC => ⟨max a (max b c), fun x hx hle i => ?_⟩⟩
  have e1 : a ≤ x := (le_max_left _ _).trans hle
  have e2 : b ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have e3 : c ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  exact ha x hx e1 i (σ Fm (w3_a hc) x hx i).pt (hb x hx e2 i) (hc' x hx e3 i) C hC
end GlobalTheory.Fc.Ind
end

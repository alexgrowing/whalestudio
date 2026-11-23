import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_action_preserves_flat_form : ∀ g : ℕ, ∀ γ : Sp g, Set.BijOn (actU γ) (cov (siegel g) g) (cov (siegel g) g) ∧ DifferentiableOn ℂ (actU γ) (cov (siegel g) g) ∧ (∀ P ∈ cov (siegel g) g, IsUnit (den γ (tauU P.1)) ∧ tauU (actU γ P).1 = moeb γ (tauU P.1) ∧ flat tauU (actU γ P) = flat tauU P ᵥ* (γ⁻¹).mat ∧ pull (actU γ) (om0 tauU) P = om0 tauU P ∧ (P.2 = 0 → (actU γ P).2 = 0)) := by
  first | exact @GlobalTheory.UnivAction.univAct | exact GlobalTheory.UnivAction.univAct | (intros; apply GlobalTheory.UnivAction.univAct <;> assumption)

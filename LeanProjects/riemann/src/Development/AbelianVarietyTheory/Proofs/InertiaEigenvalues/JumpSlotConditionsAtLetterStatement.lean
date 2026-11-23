import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpPositionConditionsAtLetter
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_position_conditions_at_letter : ∀ (l t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ) (sgP σ : ℤ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    (∀ n : ℤ, W0 + (-η - 2 * (sgP : ℝ) - 3) ≤ (n : ℝ) → (n : ℝ) ≤ W0 + (S + η + η + 2 * (sgP : ℝ) + 4) →
      ¬ (l : ℤ) ∣ n) →
    (σ : ℝ) ≤ 2 * B → σ ≤ sgP → 2 * η + 8 * B + 7 < (l : ℝ) →
    (∀ u ∈ GlobalTheory.PositionData.US up Fl Fc, 1 ≤ u ∧ u ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1) ∧
    1 ≤ GlobalTheory.PositionData.wS up Fl Fc ∧
    (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1 ∧
    (up = true → (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ GlobalTheory.PositionData.etaS t Fl) ∧
    (up = false → (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - GlobalTheory.PositionData.etaS t Fl ≤ GlobalTheory.PositionData.wS up Fl Fc) ∧
    (GlobalTheory.PositionData.etaS t Fl : ℤ) + 4 * σ + 6 < l ∧
    (∀ x ∈ Formalism.MainNotions.tableLineDegreeTwo.lows up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) (GlobalTheory.PositionData.US up Fl Fc),
      ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (GlobalTheory.PositionData.wS up Fl Fc) t, σ + 2 < |x - y|) ∧
    Formalism.WachCohomologyFacts.V2.ResidueAvoidance l up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) σ (GlobalTheory.PositionData.US up Fl Fc) := by
  first | exact @GlobalTheory.PositionData.position_conditions | exact GlobalTheory.PositionData.position_conditions | (intros; apply GlobalTheory.PositionData.position_conditions <;> assumption)

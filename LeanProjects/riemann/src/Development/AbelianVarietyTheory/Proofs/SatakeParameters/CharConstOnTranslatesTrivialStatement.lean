import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharConstOnTranslatesTrivial
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_continuous_char_const_on_translates : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : (ι → ℂˣ) →* ℂˣ) (θ : ι → ℂ) (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ), Continuous ψ → (∀ i, (θ i).im ≠ 0) → (∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C) → (∀ a ∈ T, ∀ z : ι → ℂˣ, (∀ i, (z i : ℂ) = a i + θ i) → ψ z = c) → ψ = 1 := by
  first | exact @GlobalTheory.charConstOnTranslates_trivial | exact GlobalTheory.charConstOnTranslates_trivial | (intros; apply GlobalTheory.charConstOnTranslates_trivial <;> assumption)

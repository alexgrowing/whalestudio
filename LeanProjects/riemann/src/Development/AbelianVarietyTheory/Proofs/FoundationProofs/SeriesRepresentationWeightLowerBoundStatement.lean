import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBound
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_representation_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  first | exact @GlobalTheory.BadShare.series_weight_lower_bound | exact GlobalTheory.BadShare.series_weight_lower_bound | (intros; apply GlobalTheory.BadShare.series_weight_lower_bound <;> assumption)

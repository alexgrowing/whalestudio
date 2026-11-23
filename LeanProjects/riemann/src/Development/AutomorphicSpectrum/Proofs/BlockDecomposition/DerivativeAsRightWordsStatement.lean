import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWords
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_as_right_words : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | exact GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | (intros; apply GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb <;> assumption)

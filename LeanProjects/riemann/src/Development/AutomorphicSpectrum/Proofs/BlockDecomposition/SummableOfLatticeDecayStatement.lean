import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_of_lattice_decay_of_injective : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | exact GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | (intros; apply GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay <;> assumption)

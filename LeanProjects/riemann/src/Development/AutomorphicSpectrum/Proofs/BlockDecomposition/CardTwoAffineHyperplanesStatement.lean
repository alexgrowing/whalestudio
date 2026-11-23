import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_two_affine_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k), a ≠ 0 → (∀ s : k, b ≠ s • a) →
  Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | exact GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_two_equations <;> assumption)

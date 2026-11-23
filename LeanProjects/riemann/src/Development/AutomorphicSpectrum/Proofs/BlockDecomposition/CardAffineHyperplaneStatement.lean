import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplane
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_affine_hyperplane : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | exact GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one <;> assumption)

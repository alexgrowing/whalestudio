import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFunctionalsVanishingSubspace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_functionals_vanishing_subspace : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
  Module.finrank k M + (j + 1) = n + 1 →
  (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | exact GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line <;> assumption)

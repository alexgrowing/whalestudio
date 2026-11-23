import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRank
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_map_zero_of_injective_full_rank : ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N] [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ) (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N), Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | exact GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq <;> assumption)

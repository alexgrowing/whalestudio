import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | exact GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | (intros; apply GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty <;> assumption)

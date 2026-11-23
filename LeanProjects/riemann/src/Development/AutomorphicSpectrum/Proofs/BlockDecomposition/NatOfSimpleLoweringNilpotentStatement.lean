import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_of_simple_lowering_nilpotent : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → (j : ℕ) = i + 1 → (∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) → ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | exact GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | (intros; apply GlobalTheory.CompanionTheory.PresRho.natural_of_primitive <;> assumption)

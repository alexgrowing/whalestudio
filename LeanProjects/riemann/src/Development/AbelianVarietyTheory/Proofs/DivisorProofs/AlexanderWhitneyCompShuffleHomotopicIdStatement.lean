import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicId
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  first | (exact @GlobalTheory.EZ.awThen_homotopic) | (exact GlobalTheory.EZ.awThen_homotopic) | (intros; apply GlobalTheory.EZ.awThen_homotopic <;> assumption)

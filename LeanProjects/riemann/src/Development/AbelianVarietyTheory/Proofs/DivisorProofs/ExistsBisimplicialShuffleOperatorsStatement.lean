import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperators
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bisimplicial_shuffle_operators : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧ ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  first | (exact @GlobalTheory.EZ.Shuf.exists_shuffle) | (exact GlobalTheory.EZ.Shuf.exists_shuffle) | (intros; apply GlobalTheory.EZ.Shuf.exists_shuffle  <;> assumption)

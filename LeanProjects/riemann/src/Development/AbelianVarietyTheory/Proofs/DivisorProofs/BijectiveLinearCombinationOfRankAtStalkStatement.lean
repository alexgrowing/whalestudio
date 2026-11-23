import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLinearCombinationOfRankAtStalk
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearCombination_bijective_of_rankAtStalk_eq : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M, Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ → Function.Bijective (Fintype.linearCombination R s) := by
  first | (exact @GlobalTheory.bijective_linearCombination_of_rankAtStalk) | (exact GlobalTheory.bijective_linearCombination_of_rankAtStalk) | (intros; apply GlobalTheory.bijective_linearCombination_of_rankAtStalk  <;> assumption)

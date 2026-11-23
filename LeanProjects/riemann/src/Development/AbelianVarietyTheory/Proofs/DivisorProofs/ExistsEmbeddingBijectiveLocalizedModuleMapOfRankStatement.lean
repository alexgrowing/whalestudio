import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRank

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq : ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q] (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ → (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R, ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R (b ∘ σ))) := by
  first | (exact @GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (exact GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (intros; apply GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk  <;> assumption)

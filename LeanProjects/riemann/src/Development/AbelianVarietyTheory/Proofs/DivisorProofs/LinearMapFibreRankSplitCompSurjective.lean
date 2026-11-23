import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.FibreRanks

theorem fibre_ranks : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  intro O _ M _ _ N _ _ K _ _ _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ q
    have hinj : Function.Injective (f.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : ρ ∘ₗ f = LinearMap.id := LinearMap.ext hρ
      rw [this]
      simp
    exact LinearMap.finrank_range_of_inj hinj
  · intro g q hg
    have hker := LinearMap.finrank_range_add_finrank_ker (g.baseChange q.asIdeal.ResidueField)
    have h0 : Module.finrank q.asIdeal.ResidueField
        (LinearMap.ker (g.baseChange q.asIdeal.ResidueField)) = 0 := by
      unfold fibreRank fibreDim at hg
      omega
    have hinj : Function.Injective (g.baseChange q.asIdeal.ResidueField) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.finrank_eq_zero.mp h0
    unfold fibreRank
    rw [LinearMap.baseChange_comp, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  · intro h
    exact surjective_of_fibre_rank O M N f h
  · intro _ q
    haveI : Nontrivial O := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact q.isPrime.ne_top (Subsingleton.elim _ _)
    exact Module.finrank_baseChange

end GlobalTheory.FibreRanks

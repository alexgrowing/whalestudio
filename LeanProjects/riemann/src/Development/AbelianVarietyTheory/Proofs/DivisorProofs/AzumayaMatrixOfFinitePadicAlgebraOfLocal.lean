import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrtStatement
open scoped TensorProduct
open Function

namespace GlobalTheory.AzumayaMatrixReduction

theorem of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro hloc ℓ _ A _ _ _ Λ _ _ _ _ n hn
  obtain ⟨ι, _, I, hlocI, hcop, hbot⟩ := GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot ℓ A
  refine GlobalTheory.T.algEquiv_matrix_glue_crt A Λ ι I hcop hbot n fun i => ?_
  haveI := hlocI i
  haveI : IsAzumaya (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) := GlobalTheory.T.azumaya_base_change A (A ⧸ I i) Λ
  haveI : Module.Finite ℤ_[ℓ] (A ⧸ I i) :=
    Module.Finite.of_surjective ((IsScalarTower.toAlgHom ℤ_[ℓ] A (A ⧸ I i)).toLinearMap)
      Ideal.Quotient.mk_surjective
  refine hloc ℓ (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) n ?_
  haveI : Nontrivial A := (Ideal.Quotient.mk (I i)).domain_nontrivial
  rw [Module.finrank_baseChange, hn]

end GlobalTheory.AzumayaMatrixReduction

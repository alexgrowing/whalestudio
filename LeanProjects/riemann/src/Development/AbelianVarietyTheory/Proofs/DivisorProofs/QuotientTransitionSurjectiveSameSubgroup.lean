import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.QuotTransition

theorem transition_surjective : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  intro O _ A₁ _ _ _ _ _ A₂ _ _ _ _ _ B₁ _ _ _ _ _ B₂ _ _ _ _ _ π j₁ j₂ r ρ hρ hsq hker
  let j₁' : B₁ →ₗ[O] A₁ := (j₁ : B₁ →ₐ[O] A₁).toLinearMap
  let r' : B₂ →ₗ[O] B₁ := (r : B₂ →ₐ[O] B₁).toLinearMap
  have hcomp : j₁' ∘ₗ r' = ((π.comp j₂ : B₂ →ₐc[O] A₁) : B₂ →ₐ[O] A₁).toLinearMap := by
    ext b
    exact hsq b
  have hs : Function.Surjective r' := by
    refine GlobalTheory.surjective_of_fibre_rank O B₂ B₁ r' fun q => ?_
    have hinj : Function.Injective (j₁'.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have hid : ρ ∘ₗ j₁' = LinearMap.id := LinearMap.ext hρ
      rw [hid, LinearMap.baseChange_id, LinearMap.id_apply]
    have h1 : fibreRank (j₁' ∘ₗ r') q = fibreRank r' q := by
      rw [fibreRank, fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
      exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have h2 : fibreRank j₁' q = fibreDim B₁ q := LinearMap.finrank_range_of_inj hinj
    have h3 := fibreDim_eq_ker_mul_range (π.comp j₂) q
    have h4 := fibreDim_eq_ker_mul_range j₁ q
    rw [kerIdeal_comp, ← hker, ← hcomp] at h3
    have h5 : fibreDim (A₁ ⧸ kerIdeal j₁) q ≠ 0 := fun h0 =>
      fibreDim_ne_zero (A := A₁) q (by rw [h4, h0, zero_mul])
    have h6 : fibreRank (j₁' ∘ₗ r') q = fibreRank j₁' q :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5) (h3.symm.trans h4)
    have h7 : fibreRank r' q = fibreDim B₁ q := by rw [← h1, h6, h2]
    exact h7
  exact hs

end GlobalTheory.QuotTransition

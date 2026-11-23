import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLifting
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  first | exact @GlobalTheory.LiftDeriv.exists_derivation_extending | exact GlobalTheory.LiftDeriv.exists_derivation_extending | (intros; apply GlobalTheory.LiftDeriv.exists_derivation_extending <;> assumption)

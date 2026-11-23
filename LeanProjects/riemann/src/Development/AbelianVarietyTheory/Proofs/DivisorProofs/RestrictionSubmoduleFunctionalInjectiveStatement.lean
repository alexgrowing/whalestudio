import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionSubmoduleFunctionalInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubquotientJacUIntertwining
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_submodule_functional_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (X G₁ : Type) [AddCommGroup X] [Module ℂ X] [Group G₁]
    (π : Representation ℂ (GL (Fin n) k) X) (ι : GL (Fin m) k →* G₁), Function.Injective ι →
    ∀ (U M : Submodule ℂ X) (Λ : X →ₗ[ℂ] (G₁ → ℂ)), M ≤ U → (∀ g, ∀ φ ∈ U, π g φ ∈ U) → (∀ g, ∀ φ ∈ M, π g φ ∈ M) →
      (∀ φ ∈ U, IsOpen {g | π g φ = φ}) →
      (∀ φ ∈ M, ∀ u ∈ unipRad k e, Λ (π u φ) = Λ φ) →
      (∀ φ ∈ M, ∀ h, Λ (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ φ)) →
      ∃ Λ' : X →ₗ[ℂ] (G₁ → ℂ), (∀ φ ∈ M, Λ' φ = Λ φ) ∧ (∀ φ ∈ U, ∀ u ∈ unipRad k e, Λ' (π u φ) = Λ' φ) ∧
        ∀ φ ∈ U, ∀ h, Λ' (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ' φ) := by
  first | exact @GlobalTheory.ext_sub_smooth | exact GlobalTheory.ext_sub_smooth | (intros; apply GlobalTheory.ext_sub_smooth <;> assumption)

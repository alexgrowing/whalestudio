import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAevalKernelsOrthogonalOfCoprime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_aeval_kernels_orthogonal_of_coprime : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 →
    ∀ (q₁ q₂ a b : K[X]), a * q₁ + b * q₂ = 1 → aeval γ (q₁ * q₂) = 0 →
    ∀ (V : Submodule K (Fin n → K)), (∀ x, x ∈ V ↔ aeval γ q₁ *ᵥ x = 0) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (bs : Module.Basis ι K V),
    (Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k).det ≠ 0 →
    ∀ x ∈ V, ∀ y : Fin n → K, aeval γ q₂ *ᵥ y = 0 → ∑ k, σ (x k) * y k = 0 := by
  first | exact @GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime | exact GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime | (intros; apply GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime <;> assumption)

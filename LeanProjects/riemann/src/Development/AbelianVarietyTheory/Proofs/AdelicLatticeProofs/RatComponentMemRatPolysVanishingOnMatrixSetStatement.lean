import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, MvPolynomial.coeff m f' = l (MvPolynomial.coeff m f)) → f' ∈ vanI Γ := by
  first | exact @GlobalTheory.ClassFin.component_mem_vanI | exact GlobalTheory.ClassFin.component_mem_vanI | (intros; apply GlobalTheory.ClassFin.component_mem_vanI <;> assumption)

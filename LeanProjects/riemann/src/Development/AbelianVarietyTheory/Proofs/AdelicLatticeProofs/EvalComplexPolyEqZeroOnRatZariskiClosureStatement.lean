import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ y ∈ pts Γ ℂ, evC f y = 0 := by
  first | exact @GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | exact GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | (intros; apply GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable <;> assumption)

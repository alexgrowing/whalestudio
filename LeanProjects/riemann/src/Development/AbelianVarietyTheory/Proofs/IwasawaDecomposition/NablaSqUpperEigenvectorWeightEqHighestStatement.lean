import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  first | exact @GlobalTheory.HwEigen.mu_eq_of_upper_eigen | exact GlobalTheory.HwEigen.mu_eq_of_upper_eigen | (intros; apply GlobalTheory.HwEigen.mu_eq_of_upper_eigen <;> assumption)

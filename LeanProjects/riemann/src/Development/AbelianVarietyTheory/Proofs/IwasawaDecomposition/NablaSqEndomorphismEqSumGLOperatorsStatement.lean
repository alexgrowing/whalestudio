import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperators
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaSq_endomorphism_eq_sum_GL_operators : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N),
    (∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam) →
    ∀ φ : nablaSq k N lam →ₗ[k] nablaSq k N lam, ∃ (s : Finset (GL (Fin N) k)) (c : GL (Fin N) k → k),
      ∀ f : nablaSq k N lam, (φ f : MvPolynomial (Fin N × Fin N) k) = ∑ g ∈ s, c g • sqAct k N lam g f := by
  first | exact @GlobalTheory.NablaDensity.endo_eq_sum_sqAct | exact GlobalTheory.NablaDensity.endo_eq_sum_sqAct | (intros; apply GlobalTheory.NablaDensity.endo_eq_sum_sqAct <;> assumption)

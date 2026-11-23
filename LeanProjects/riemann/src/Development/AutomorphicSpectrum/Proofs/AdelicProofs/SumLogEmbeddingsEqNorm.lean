import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem sum_log_norm_embeddings_eq_log_norm (k A : Type) [Field k] [NumberField k] [NormedField A]
    [CharZero A] [IsAlgClosed A] (x : k) (hx : x ≠ 0) :
    ∑ j : k →+* A, Real.log ‖j x‖ = Real.log ‖((Algebra.norm ℚ x : ℚ) : A)‖ := by
  letI : Algebra ℚ A := DivisionRing.toRatAlgebra
  have h1 : algebraMap ℚ A (Algebra.norm ℚ x) = ∏ σ : k →ₐ[ℚ] A, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ A x
  have h2 : ((Algebra.norm ℚ x : ℚ) : A) = ∏ σ : k →ₐ[ℚ] A, σ x := by
    rw [← h1]; simp
  have h3 : ∏ σ : k →ₐ[ℚ] A, σ x = ∏ j : k →+* A, j x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := k) (S := A)).symm _ _ (fun σ => rfl)
  rw [h2, h3, norm_prod, Real.log_prod]
  intro j _
  exact norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hx)

end GlobalTheory.CompanionTheory.Ar.Fl

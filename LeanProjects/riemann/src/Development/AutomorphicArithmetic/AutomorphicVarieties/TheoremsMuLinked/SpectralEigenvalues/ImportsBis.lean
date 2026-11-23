import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreFurther
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.ell :
    ∀ (O Λ Γ X : Type) [CommRing O] [CommRing Λ] [Algebra O Λ] [CommGroup Γ] [AddCommGroup X] [Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X) (χ : Γ →* Multiplicative X), (∀ a b, d (a * b) = th₀ a • d b + th₀ b • d a) → ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X), (∀ g a, th (MonoidAlgebra.single g a) = th₀ a) ∧ (∀ a b, ell (a * b) = th a • ell b + th b • ell a) ∧ ∀ g a, ell (MonoidAlgebra.single g a) = d a + th₀ a • Multiplicative.toAdd (χ g) :=
  _root_.UpperTheory.Reformulated.B.Qh12.ell

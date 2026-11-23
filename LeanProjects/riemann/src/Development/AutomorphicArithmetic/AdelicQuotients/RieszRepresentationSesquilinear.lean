import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RieszRepresentationSesquilinear

theorem UpperTheory.riesz_representation_sesquilinear :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ a b, B b a = star (B a b)) → (∀ a, a ≠ 0 → 0 < (B a a).re) → ∀ L : V →ₗ⋆[ℂ] ℂ, ∃ u, ∀ b, L b = B u b :=
  _root_.UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear

import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurableOfSeparatingFunctionals

theorem UpperTheory.measurable_of_separating_functionals :
    ∀ {G V ι : Type} [MeasurableSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ι → V →ₗ[ℂ] ℂ), (∀ a, (∀ y, l y a = 0) → a = 0) → ∀ T : G → V, (∀ y, Measurable fun g => l y (T g)) → ∀ L : V →ₗ[ℂ] ℂ, Measurable fun g => L (T g) :=
  _root_.UpperTheory.Reformulated.B.Qk65.measurable_of_separating_functionals

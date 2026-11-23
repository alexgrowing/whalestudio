import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_chart_existsUnique_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 → ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime → ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), s ∉ I ↔ unitAt ξ p (s : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.chart_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_point_of_prime <;> assumption)

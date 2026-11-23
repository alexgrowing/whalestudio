import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonal
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure | exact GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure | (intros; apply GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure <;> assumption)

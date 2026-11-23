import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  first | exact @GlobalTheory.ThFamRead.exists_reading | exact GlobalTheory.ThFamRead.exists_reading | (intros; apply GlobalTheory.ThFamRead.exists_reading <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perCoord : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  first | exact @GlobalTheory.PerCoordU.perCoord_exists | exact GlobalTheory.PerCoordU.perCoord_exists | (intros; apply GlobalTheory.PerCoordU.perCoord_exists <;> assumption)

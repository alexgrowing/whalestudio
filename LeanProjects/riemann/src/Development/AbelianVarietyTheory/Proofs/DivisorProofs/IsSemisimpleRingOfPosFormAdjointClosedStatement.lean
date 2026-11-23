import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemisimpleRingOfPosFormAdjointClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleRing_of_posDef_adjoint_closed : ∀ (r : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ)), Q.IsHermitian → (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) → (∀ x ∈ S, ∃ y ∈ S, Q * y = xᴴ * Q) → IsSemisimpleRing S := by
  first | exact @GlobalTheory.isSemisimpleRing_of_posForm_adjoint_closed | exact GlobalTheory.isSemisimpleRing_of_posForm_adjoint_closed | (intros; apply GlobalTheory.isSemisimpleRing_of_posForm_adjoint_closed <;> assumption)

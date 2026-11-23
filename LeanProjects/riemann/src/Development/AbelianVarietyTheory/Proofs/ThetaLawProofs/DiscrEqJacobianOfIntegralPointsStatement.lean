import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscrEqJacobianOfIntegralPoints
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_discr_associated_prod_jacobian : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix] [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O)) (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) → (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) → ∃ β : Ix → (MvPowerSeries (Fin g) O), (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧ (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧ Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by
  first | exact @GlobalTheory.KeyKa.discr_jacobian_of_points | exact GlobalTheory.KeyKa.discr_jacobian_of_points | (intros; apply GlobalTheory.KeyKa.discr_jacobian_of_points <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G), IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  first | exact @GlobalTheory.ExpLin.existsUnique_linear_lift | exact GlobalTheory.ExpLin.existsUnique_linear_lift | (intros; apply GlobalTheory.ExpLin.existsUnique_linear_lift <;> assumption)

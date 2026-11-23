import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponential
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  first | exact @GlobalTheory.exists_riemannForm_of_relAmple | exact GlobalTheory.exists_riemannForm_of_relAmple | (intros; apply GlobalTheory.exists_riemannForm_of_relAmple <;> assumption)

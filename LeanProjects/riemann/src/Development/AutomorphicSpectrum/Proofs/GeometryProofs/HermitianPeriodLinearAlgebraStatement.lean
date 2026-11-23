import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_period_linear_algebra : ∀ (p q g : ℕ) (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ) (π : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ), IsLinearMap ℂ T → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → S.det ≠ 0 → LinearIndependent ℂ V → LinearIndependent ℂ W → (∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) → (∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W)) → (∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n) → ∃! x : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × ℂ, (∀ n, T' (π n) = ∑ j, x.2.1 j n • W j) ∧ (∀ j n, ∑ m, x.1 j m * S m n = x.2.1 j n) ∧ x.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • π m) = V a) ∧ ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • π m) = V a) → (Matrix.fromRows C x.1).det = x.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | exact GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra <;> assumption)

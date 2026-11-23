import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefConeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBoundStatement
import Development.WeilBound.CoreStatements.FlagImmersions.TowerRationalWeightBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem deg_bounds : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam :=
  RootFieldNumerics.tower_rational_weight_bound

end GlobalTheory.CompanionTheory.Ar.Top

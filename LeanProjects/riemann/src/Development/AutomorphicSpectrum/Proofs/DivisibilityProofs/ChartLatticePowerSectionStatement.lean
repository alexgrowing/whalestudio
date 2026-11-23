import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_power_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm <;> assumption)

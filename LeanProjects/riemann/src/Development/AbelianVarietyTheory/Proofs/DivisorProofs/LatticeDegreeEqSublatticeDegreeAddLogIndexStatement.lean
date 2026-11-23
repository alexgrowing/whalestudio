import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | exact GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | (intros; apply GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralSectionLatticeMultiple
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_section_lattice_multiple : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) [CharZero Ω] (d : ℕ) (a : K → ℤ) (s : Ω), (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))) → ∃ N₀ : ℕ, 0 < N₀ ∧ (N₀ : Ω) * s ∈ chartLatNm y a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_nat_mul_mem_chartLatNm_of_isIntegral_rat | exact GlobalTheory.CompanionTheory.Ar.Small.exists_nat_mul_mem_chartLatNm_of_isIntegral_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_nat_mul_mem_chartLatNm_of_isIntegral_rat <;> assumption)

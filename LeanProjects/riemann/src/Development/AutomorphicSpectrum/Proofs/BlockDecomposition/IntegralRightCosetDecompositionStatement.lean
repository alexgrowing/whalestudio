import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightCosetDecomposition
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_coset_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
  (∀ a b, R a * (R b)⁻¹ ∈ K → a = b) → (∀ κ ∈ K, ∀ g, f (κ * g) = f g) →
  (∀ g, f g ≠ 0 → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
  ∫ g, f g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ a ∈ S, f (R a) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets | exact GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets | (intros; apply GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets <;> assumption)

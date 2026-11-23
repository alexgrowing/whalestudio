import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTwoStepUnfoldingSemidirectLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectAverageIndicatorLowerBoundStatement
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem modulus_mul_measure_shell_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM hL μ D hμ hD C hC
  obtain ⟨U, c, hU, hμU, hc, hlow⟩ := GlobalTheory.T.semidirectAverage_indicator_lower_bound G N M Λ ν π DN DM hL μ hμ C hC
  have hX : ν DN * π DM * μ U ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hL.finN hL.finM) hμU
  refine ⟨ν DN * π DM * μ U / c, ENNReal.div_ne_top hX hc, ?_⟩
  intro b κ hb hκ S hS hSx
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inr hX)]
  have hφ : Measurable (U.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have hw := GlobalTheory.T.lintegral_two_step_unfolding_semidirect_lattice G N M Λ ν π DN DM hL μ D hμ hD
    (fun x => U.indicator (1 : G → ℝ≥0∞) (b * x)) (hφ.comp (measurable_const_mul b))
  rw [lintegral_mul_left_eq_self (U.indicator (1 : G → ℝ≥0∞)) b,
    lintegral_indicator_one hU.measurableSet] at hw
  rw [← hw]
  have h1 : κ * μ (S ∩ D) * c = ∫⁻ x in D, S.indicator (fun _ => κ * c) x ∂μ := by
    rw [lintegral_indicator_const hS, Measure.restrict_apply hS]; ring
  rw [h1]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    obtain ⟨u₀, hu₀, m₀, hm₀, y, hy, hxy⟩ := hSx x hx
    have h2 := hlow u₀ hu₀ m₀ hm₀ y hy
    rw [← hxy] at h2
    refine le_trans (mul_le_mul_right h2 κ) (le_trans (lintegral_const_mul_le _ _) (le_of_eq ?_))
    refine lintegral_congr fun m => ?_
    have h3 := hκ (fun g => U.indicator (1 : G → ℝ≥0∞) (g * m * (b * x)))
      (hφ.comp ((measurable_id.mul_const _).mul_const _))
    rw [← h3]
    refine lintegral_congr fun u => ?_
    congr 1
    have h4 := hb m m.2
    calc b * (u : G) * b⁻¹ * m * (b * x) = b * u * b⁻¹ * (m * b) * x := by group
      _ = b * u * b⁻¹ * (b * m) * x := by rw [h4]
      _ = b * (u * m * x) := by group
  · rw [Set.indicator_of_notMem hx]; exact zero_le

end GlobalTheory.ResLine

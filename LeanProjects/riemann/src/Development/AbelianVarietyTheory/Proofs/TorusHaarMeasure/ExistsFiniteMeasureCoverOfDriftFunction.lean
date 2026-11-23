import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteCovolumeOfDriftFunction
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem exists_finite_measure_cover_of_drift_function : (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) :=
  GlobalTheory.finite_covolume_of_drift_function GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift
    GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete GlobalTheory.haar_map_mul_right_of_conj_inv
    GlobalTheory.fundamentalSet_lintegral_mul_right_and_measure_le

end GlobalTheory

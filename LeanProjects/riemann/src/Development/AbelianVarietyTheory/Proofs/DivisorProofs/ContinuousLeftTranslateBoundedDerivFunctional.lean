import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem SmFn.continuous_leftTranslate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK Λ hΛ l f hf
  haveI := h.locallyCompactSpace
  haveI : SecondCountableTopology 𝔸ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨C, hC⟩ := hΛ.bdd l
  rw [continuous_iff_continuousAt]
  intro x₀
  have hfc := hS f hf
  have hcont : Continuous fun x : G => ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun x y : G => ‖f (x * y) - f (x₀ * y)‖)
      (((hfc.comp (continuous_fst.mul continuous_snd)).sub
        (hfc.comp (continuous_const.mul continuous_snd))).norm) hK
  have h0 : Filter.Tendsto (fun x : G => C * ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ) (nhds x₀) (nhds 0) := by
    have := (hcont.const_mul C).tendsto x₀
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h0
  have h1 := hΛ.lin l _ (hL f hf x₀) _ (hL f hf x) (-1)
  have h2 := hC _ (S.add_mem (S.smul_mem (-1 : ℂ) (hL f hf x₀)) (hL f hf x))
  rw [h1] at h2
  simpa [neg_add_eq_sub] using h2

end GlobalTheory.HCA

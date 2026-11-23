import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem fubini_right_convolution_bounded_continuous
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G)
    (h𝓕 : μ 𝓕 < ⊤) (m : Measure H) [SFinite m] (α : H → ℂ) (hα : Integrable α m)
    (ψ φ : G → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) (A B : ℝ)
    (hA : ∀ g, ‖ψ g‖ ≤ A) (hB : ∀ g, ‖φ g‖ ≤ B) :
    IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧
    Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧
    ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ
      = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simpa [Measure.restrict_apply_univ] using h𝓕⟩
  set F : G → H → ℂ := fun x h => ψ x * (α h * φ (x * (h : G))) with hFdef
  have hcont : Continuous (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) :=
    (hψ.comp continuous_fst).mul (hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    have h1 : AEStronglyMeasurable (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) ((μ.restrict 𝓕).prod m) :=
      hcont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : G × H => α p.2) ((μ.restrict 𝓕).prod m) :=
      hα.aestronglyMeasurable.comp_snd
    refine (h1.mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, Pi.mul_apply]; ring
  have hbd : Integrable (fun p : G × H => (1 : ℝ) * ((A * B) * ‖α p.2‖)) ((μ.restrict 𝓕).prod m) :=
    (integrable_const (1 : ℝ)).mul_prod (hα.norm.const_mul (A * B))
  have hint : Integrable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    refine hbd.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, norm_mul, one_mul]
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
    calc ‖ψ p.1‖ * (‖α p.2‖ * ‖φ (p.1 * (p.2 : G))‖) ≤ A * (‖α p.2‖ * B) := by
          gcongr
          · exact hA _
          · exact hB _
      _ = A * B * ‖α p.2‖ := by ring
  have hL : ∀ x, ∫ h, F x h ∂m = ψ x * ∫ h, α h * φ (x * (h : G)) ∂m := fun x =>
    integral_const_mul _ _
  have hR : ∀ h : H, ∫ x in 𝓕, F x h ∂μ = α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ := by
    intro h
    rw [← integral_const_mul]
    congr 1; funext x; simp only [hFdef]; ring
  refine ⟨?_, ?_, ?_⟩
  · have := hint.integral_prod_left
    exact (by simpa [Function.uncurry, hL] using this : Integrable _ (μ.restrict 𝓕))
  · have := hint.integral_prod_right
    simpa [Function.uncurry, hR] using this
  · have := integral_integral_swap hint
    simpa [hL, hR] using this

end GlobalTheory

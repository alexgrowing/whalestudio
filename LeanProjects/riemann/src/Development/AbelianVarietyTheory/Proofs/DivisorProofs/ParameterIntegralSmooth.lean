import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory

theorem contDiffOn_integral_mul_kernel_of_compact :
    ∀ (d : ℕ) (U' C : Set (Fin d → ℂ)) (K : (Fin d → ℂ) × (Fin d → ℂ) → ℝ) (ψ : (Fin d → ℂ) → ℝ),
      IsOpen U' → IsCompact C → (∀ z ∈ U', ∀ w, w ∉ C → K (z, w) = 0) →
      MeasureTheory.IntegrableOn ψ C MeasureTheory.volume →
      ContDiffOn ℝ ∞ K (U' ×ˢ Set.univ) →
      ContDiffOn ℝ ∞ (fun z => ∫ w, ψ w * K (z, w)) U' := by
  intro d U' C K ψ hU hC hK hψ hKs
  have hf : LocallyIntegrable (C.indicator ψ) volume :=
    ((integrable_indicator_iff hC.measurableSet).2 hψ).locallyIntegrable
  have hgs : ∀ p, ∀ x, p ∈ U' → x ∉ -C → (fun z (y : Fin d → ℂ) => K (z, -y)) p x = 0 := by
    intro p x hp hx
    exact hK p hp (-x) (by simpa [Set.mem_neg] using hx)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿(fun z (y : Fin d → ℂ) => K (z, -y))) (U' ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => (p.1, -p.2)) :=
      contDiff_fst.prodMk contDiff_snd.neg
    refine hKs.comp h1.contDiffOn ?_
    rintro ⟨p, x⟩ ⟨hp, -⟩
    exact ⟨hp, Set.mem_univ _⟩
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Fin d → ℂ => (0 : Fin d → ℂ)) U' := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℝ) hv hU hC.neg hgs hf hg
  refine main.congr ?_
  intro z hz
  simp only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub, neg_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ C
  · simp [Set.indicator_of_mem hw]
  · simp [Set.indicator_of_notMem hw, hK z hz w hw]

end GlobalTheory

import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.norm_trace_comp_le_mul_traceNorm :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ι : Type) (b : HilbertBasis ι ℂ H) (T D : H →L[ℂ] H) (c : ℝ), 0 ≤ c → IsTraceClass T → (∀ i, ∃ d : ℂ, ‖d‖ ≤ c ∧ T (D (b i)) = d • T (b i)) → ‖trace (D ∘L T)‖ ≤ c * (traceNorm T).toReal := by
  intro H _ _ _ ι b T D c hc hT hd
  have hs := hT.summable_norm_inner b
  have h1 := (hT.comp_right D).hasSum_trace b
  rw [trace_comp_comm hT D]
  have h2 : ‖trace (T ∘L D)‖ ≤ ∑' i, c * ‖inner ℂ (b i) (T (b i))‖ :=
    h1.norm_le_of_bounded (hs.mul_left c).hasSum fun i => by
      obtain ⟨d, hd1, hd2⟩ := hd i
      rw [ContinuousLinearMap.comp_apply, hd2, inner_smul_right, norm_mul]
      exact mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
  have h3 : ∑' i, ‖inner ℂ (b i) (T (b i))‖ ≤ (traceNorm T).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal (show traceNorm T < ⊤ from hT).ne,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    simp only [ofReal_norm]
    exact tsum_enorm_inner_self_le b T
  rw [tsum_mul_left] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h3 hc)

import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem norm_le_of_sq {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (h : t ^ 2 ≤ B * t) : t ≤ B := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem UpperTheory.ConvolutionTheory.K.kvBd :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n),
      (PolyBd μ a → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x, ‖kv μ a x‖ ≤ C * qht x ^ N) ∧
      (CuspDecay μ a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Pc μ (kv μ a x)‖ ≤ C * (qht x ^ N')⁻¹) := by
  intro K _ _ n μ _ a
  have hq : ∀ x : G1 K n, 0 ≤ qht x := fun x => zero_le_one.trans ((qhtBasic K n).1 x)
  refine ⟨?_, ?_⟩
  · rintro ⟨C, N, h⟩
    refine ⟨max C 0, N, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ qht x ^ N := pow_nonneg (hq x) N
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have h1 := h (kv μ a x) x
    rw [← inner_kv, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖kv μ a x‖ ^ 2 ≤ C * qht x ^ N * ‖kv μ a x‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _
  · intro hc N'
    obtain ⟨C, h⟩ := hc N'
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (hq x) N')
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have hm : Pc μ (kv μ a x) ∈ cuspidalL2 μ := Submodule.starProjection_apply_mem _ _
    have h1 := h (Pc μ (kv μ a x)) hm x
    have h0 : ⟪kv μ a x - Pc μ (kv μ a x), Pc μ (kv μ a x)⟫_ℂ = 0 :=
      Submodule.starProjection_inner_eq_zero _ _ hm
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [← inner_kv, h0, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖Pc μ (kv μ a x)‖ ^ 2 ≤ C * (qht x ^ N')⁻¹ * ‖Pc μ (kv μ a x)‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _

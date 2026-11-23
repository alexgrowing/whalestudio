import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTw :
    UpperTheory.V.Af.Smo.SchTensor → UpperTheory.V.Af.Smo.SchTw := by
  intro hT V M _ _ _ _ _ _ A e
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩
    have h0 : 0 ≤ ‖A‖ := norm_nonneg _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2 := by
    intro ξ hξ
    calc ‖A (ξ - e)‖ ≤ ‖A‖ * ‖ξ - e‖ := A.le_opNorm _
      _ ≤ ‖A‖ * δ := by
        gcongr
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hξ).le
      _ ≤ 1 / 2 := hAδ
  let φ : ContDiffBump e := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let χ : ContDiffBump e := ⟨δ / 2, δ, by positivity, by linarith⟩
  let g : V → (M →L[ℝ] M) := fun ξ => χ ξ • A (ξ - e)
  have hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2 := by
    intro ξ
    by_cases hξ : χ ξ = 0
    · simp [g, hξ]
    · have hmem : ξ ∈ Metric.ball e δ := by
        have h1 : ξ ∈ Function.support χ := hξ
        rwa [χ.support_eq] at h1
      simp only [g]
      rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
      calc χ ξ * ‖A (ξ - e)‖ ≤ 1 * (1 / 2) := by
            gcongr
            · exact χ.le_one
            · exact hball ξ hmem
        _ = 1 / 2 := by norm_num
  refine ⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h1 : φ e = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp [h1]
  · intro ξ hξ y hy
    have hφ : φ ξ ≠ 0 := by
      intro h1
      apply hξ
      simp [h1]
    have hmem : ξ ∈ Metric.ball e δ := by
      have h1 : ξ ∈ Function.support φ := hφ
      rw [φ.support_eq] at h1
      exact Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1
    have h2 : y = -(A (ξ - e)) y := eq_neg_of_add_eq_zero_left hy
    have h3 : ‖y‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖y‖ = ‖(A (ξ - e)) y‖ := by
            conv_lhs => rw [h2]
            exact norm_neg _
        _ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y
        _ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)
    have h4 : ‖y‖ = 0 := le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp h4
  · intro α
    have hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    obtain ⟨G0, hG0⟩ := hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α
    have hg : Function.HasTemperateGrowth g := by
      apply HasCompactSupport.hasTemperateGrowth
      · exact χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))
      · exact χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))
    let Φ : V × M → V × M := fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)
    have hΦ : Function.HasTemperateGrowth Φ := by
      have h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1) :=
        hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
      have h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2) :=
        (ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1
          (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
      exact Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id
        ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)
    have hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2) := by
      intro p
      ext <;> simp [Φ]
    have hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k := by
      refine ⟨1, 2, fun p => ?_⟩
      have e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖ := by
        simpa using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)
      have e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖ :=
        ((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))
      have e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_snd_le (p.1, p.2 + g p.1 p.2)
      have e4 : ‖p.1‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_fst_le (p.1, p.2 + g p.1 p.2)
      rw [pow_one]
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]
    refine ⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩
    rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]
    by_cases hφ : φ ξ = 0
    · simp [hφ]
    · have hmem : ξ ∈ Metric.closedBall e χ.rIn := by
        have h1 : ξ ∈ Function.support φ := hφ
        rw [φ.support_eq] at h1
        exact Metric.ball_subset_closedBall h1
      simp [g, χ.one_of_mem_closedBall hmem]

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

theorem tendsto_mean_ball_of_continuousAt {r : ℕ} (c : Fin r → ℂ) (f : (Fin r → ℂ) → ℝ≥0∞)
    (hf : ContinuousAt f c) (h1 : f c = 1) :
    Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball c ρ, f x) / volume (Metric.ball (0 : Fin r → ℂ) ρ))
      (𝓝[>] 0) (𝓝 1) := by
  rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
  intro ε hε
  have hfc : Tendsto f (𝓝 c) (𝓝 1) := by rw [← h1]; exact hf
  have hev := (ENNReal.tendsto_nhds ENNReal.one_ne_top).1 hfc ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hV : volume (Metric.ball c ρ) = volume (Metric.ball (0 : Fin r → ℂ) ρ) :=
    Measure.addHaar_ball_center volume c ρ
  have hpos : volume (Metric.ball c ρ) ≠ 0 := (Metric.measure_ball_pos volume c hρ.1).ne'
  have hfin : volume (Metric.ball c ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hsub : ∀ x ∈ Metric.ball c ρ, f x ∈ Set.Icc (1 - ε) (1 + ε) := fun x hx =>
    hball x (Metric.ball_subset_ball hρ.2.le hx)
  have hlo : (1 - ε) * volume (Metric.ball c ρ) ≤ ∫⁻ x in Metric.ball c ρ, f x := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).1
  have hhi : ∫⁻ x in Metric.ball c ρ, f x ≤ (1 + ε) * volume (Metric.ball c ρ) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).2
  rw [← hV]
  constructor
  · calc 1 - ε = (1 - ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          (ENNReal.mul_div_cancel_right hpos hfin).symm
      _ ≤ _ := ENNReal.div_le_div_right hlo _
  · calc _ ≤ (1 + ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          ENNReal.div_le_div_right hhi _
      _ = 1 + ε := ENNReal.mul_div_cancel_right hpos hfin

theorem tendsto_mean_cWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  intro k r
  apply tendsto_mean_ball_of_continuousAt
  · refine (ENNReal.continuous_ofReal.comp ?_).continuousAt
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  · unfold Formalism.FourierDecayAlt.B2.cWeight
    simp

end GlobalTheory.CellDens

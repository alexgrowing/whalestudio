import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.S.Pv.SchurTens

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]

private theorem aestronglyMeasurable_norm_sq {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) μ := by
  exact hu.norm.pow 2

theorem memLp_two_of_lintegral {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩
  have e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_of_nonneg (by positivity), enorm_sq_eq]
  rw [hasFiniteIntegral_iff_enorm]
  simp only [e]
  exact h

theorem lintegral_sq_eq {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2 := ae_of_all _ fun x => by
    exact sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.1)]
  congr 1
  exact lintegral_congr fun x => (enorm_sq_eq (u x)).symm

private theorem norm_conj_complex (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z

theorem integrable_mul_conj {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ :=
    hu.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)
  refine (hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖
  rw [norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
    mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]

private theorem mul_le_weighted_sq_add_half {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have ht1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t := by
    linear_combination (t * a ^ 2 - 2 * a * b) * ht1
  linarith

theorem norm_integral_mul_conj_le {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤ (t * ∫ x, ‖u x‖ ^ 2 ∂μ + (∫ x, ‖v x‖ ^ 2 ∂μ) / t) / 2 := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ :=
    ((hu2.const_mul t).add (hv2.div_const t)).div_const 2
  have h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ
      = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2 := integral_div _ _
  have h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ
      = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ :=
    integral_add (hu2.const_mul t) (hv2.div_const t)
  have h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ := integral_const_mul _ _
  have h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t := integral_div _ _
  rw [← h4, ← h3, ← h2, ← h1]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2
  rw [norm_mul, norm_conj_complex]
  exact mul_le_weighted_sq_add_half ht

private theorem lintegral_enorm_sub_limit_sq_le {f : ℕ → X → ℂ} {F : X → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) (n N : ℕ) {ε : ℝ≥0∞}
    (h : ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε) :
    ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ ≤ ε := by
  have hlim : ∀ x, Tendsto (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop (𝓝 (‖F x - f n x‖ₑ ^ 2)) := by
    intro x
    have h1 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (F x - f n x)) := (hpt x).sub_const _
    have h2 : Tendsto (fun m => ‖f m x - f n x‖ₑ) atTop (𝓝 ‖F x - f n x‖ₑ) :=
      (continuous_enorm.tendsto _).comp h1
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h2
  have hmeas : ∀ m, AEMeasurable (fun x => ‖f m x - f n x‖ₑ ^ 2) μ := fun m =>
    (((hf m).sub (hf n)).enorm).pow_const 2
  have hfreq : ∃ᶠ m in atTop, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε :=
    (eventually_atTop.2 ⟨N, h⟩).frequently
  calc ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, liminf (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' (f := fun m x => ‖f m x - f n x‖ₑ ^ 2) hmeas
    _ ≤ ε := liminf_le_of_frequently_le' hfreq

theorem limit_memLp_and_integral_eq (f : ℕ → X → ℂ) (F g : X → ℂ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hFm : AEStronglyMeasurable F μ)
    (hg : MemLp g 2 μ) (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε)
    {L : ℂ} (hL : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 L)) :
    MemLp F 2 μ ∧ Integrable (fun x => F x * conj (g x)) μ ∧ ∫ x, F x * conj (g x) ∂μ = L := by
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n => (hf2 n).1
  obtain ⟨N₀, hN₀⟩ := hC 1 one_pos
  have h0 := lintegral_enorm_sub_limit_sq_le hfm hpt N₀ N₀ (hN₀ N₀ le_rfl)
  have hsub0 : MemLp (fun x => F x - f N₀ x) 2 μ :=
    memLp_two_of_lintegral (hFm.sub (hf2 N₀).1) (lt_of_le_of_lt h0 ENNReal.one_lt_top)
  have hF : MemLp F 2 μ := by
    have hadd := hsub0.add (hf2 N₀)
    convert hadd using 1
    funext x
    simp
  have hFg : Integrable (fun x => F x * conj (g x)) μ := integrable_mul_conj hF hg
  refine ⟨hF, hFg, ?_⟩
  have hlim : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 (∫ x, F x * conj (g x) ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨G, hGe⟩ : ∃ G, ∫ x, ‖g x‖ ^ 2 ∂μ = G := ⟨_, rfl⟩
    have hG : 0 ≤ G := by
      rw [← hGe]
      exact integral_nonneg fun x => sq_nonneg _
    have hc : 0 < G + 1 := by linarith
    have hB : 0 < δ ^ 2 / (2 * (G + 1)) := div_pos (pow_pos hδ 2) (mul_pos two_pos hc)
    obtain ⟨N, hN⟩ := hC (ENNReal.ofReal (δ ^ 2 / (2 * (G + 1)))) (ENNReal.ofReal_pos.2 hB)
    refine ⟨N, fun n hn => ?_⟩
    show dist (∫ x, f n x * conj (g x) ∂μ) (∫ x, F x * conj (g x) ∂μ) < δ
    have hsub : MemLp (fun x => F x - f n x) 2 μ := hF.sub (hf2 n)
    have hlin := lintegral_enorm_sub_limit_sq_le hfm hpt n N (hN n hn)
    have hA : ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ ^ 2 / (2 * (G + 1)) := by
      rw [lintegral_sq_eq hsub]
      exact ENNReal.toReal_le_of_le_ofReal hB.le hlin
    have ht : 0 < (G + 1) / δ := div_pos hc hδ
    have hbound := norm_integral_mul_conj_le hsub hg ht
    rw [hGe] at hbound
    have hdiff : ∫ x, F x * conj (g x) ∂μ - ∫ x, f n x * conj (g x) ∂μ
        = ∫ x, (F x - f n x) * conj (g x) ∂μ := by
      rw [← integral_sub hFg (integrable_mul_conj (hf2 n) hg)]
      congr 1
      funext x
      ring
    rw [dist_eq_norm, norm_sub_rev, hdiff]
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hc0 : G + 1 ≠ 0 := hc.ne'
    have h1 : (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ / 2 := by
      calc (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ
          ≤ (G + 1) / δ * (δ ^ 2 / (2 * (G + 1))) := mul_le_mul_of_nonneg_left hA ht.le
        _ = δ / 2 := by field_simp
    have h2 : G / ((G + 1) / δ) < δ := by
      rw [div_div_eq_mul_div]
      rw [div_lt_iff₀ hc]
      nlinarith
    linarith
  exact tendsto_nhds_unique hlim hL

end Formalism.L2.S.Pv.SchurTens

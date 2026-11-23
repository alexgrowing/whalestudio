import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem eLpNorm_two_le_ofReal_sqrt_of_integral_le {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) {c : ℝ}
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have h3 : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [h3, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by norm_num)

theorem memLp_two_and_tendsto_of_cauchy_of_ae_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (v : ℕ → X → E) (u : X → E) (K : ℝ), (∀ n, MemLp (v n) 2 μ) → (∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u x))) → (∀ n m : ℕ, n ≤ m → ∫ x, ‖v n x - v m x‖ ^ 2 ∂μ ≤ K / ((n : ℝ) + 1)) → MemLp u 2 μ ∧ Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) := by
  intro X _ μ E _ v u K hv hlim hC
  have hu : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hv n).1) hlim
  have hb : ∀ n, eLpNorm (v n - u) 2 μ ≤ ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1))) := by
    intro n
    have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := μ) (p := 2) (f := fun m => v n - v m)
      (fun m => ((hv n).sub (hv m)).1) (v n - u)
      (by
        filter_upwards [hlim] with x hx
        exact tendsto_const_nhds.sub hx)
    refine hF.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact eLpNorm_two_le_ofReal_sqrt_of_integral_le ((hv n).sub (hv m)) (hC n m hm)
  refine ⟨?_, ?_⟩
  · have h0 : MemLp (v 0 - u) 2 μ :=
      ⟨(hv 0).1.sub hu, (hb 0).trans_lt ENNReal.ofReal_lt_top⟩
    have := (hv 0).sub h0
    simpa using this
  · have h1 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (h1.sqrt)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => bot_le) hb

end GlobalTheory

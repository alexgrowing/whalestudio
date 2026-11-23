import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem tendsto_ratioAt_of_ball {ε : Fin n → Bool} {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      Formalism.REAL.muG ε (expSet ε (Metric.ball (0 : gLie ε) ρ)) = ENNReal.ofReal c * ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t) :
    Tendsto (ratioAt ε) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set δ : ℝ := min (1 / 2) (e / (2 * c)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos he (by linarith))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδe : c * δ < e := by
    have : δ ≤ e / (2 * c) := min_le_right _ _
    calc c * δ ≤ c * (e / (2 * c)) := mul_le_mul_of_nonneg_left this hc.le
      _ = e / 2 := by field_simp
      _ < e := by linarith
  have hJc := (continuous_chartJac_thetaExp ε).continuousAt (x := 0)
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 hJc δ hδpos
  refine ⟨min η s, lt_min hη hs, fun ρ hρpos hρd => ?_⟩
  have hρ0 : 0 < ρ := hρpos
  have hρd' : ρ < min η s := by
    have : dist ρ 0 < min η s := hρd
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at this
  have hρη : ρ ≤ η := (lt_of_lt_of_le hρd' (min_le_left _ _)).le
  have hρr : ρ ≤ s := (lt_of_lt_of_le hρd' (min_le_right _ _)).le
  have hbound : ∀ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, |chartJac (thetaExp ε) t - 1| < δ := by
    intro t ht
    have := hcont (lt_of_lt_of_le ht hρη)
    rw [chartJac_thetaExp_zero, Real.dist_eq] at this
    exact this
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ) with hV
  have hVpos : 0 < V := Metric.measure_ball_pos volume 0 hρ0
  have hVfin : V ≠ ⊤ := measure_ball_lt_top.ne
  set I := ∫⁻ t in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (chartJac (thetaExp ε) t) with hI
  have hup : I ≤ ENNReal.ofReal (1 + δ) * V := by
    calc I ≤ ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (1 + δ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbound x hx)).2])
      _ = ENNReal.ofReal (1 + δ) * V := setLIntegral_const _ _
  have hlo : ENNReal.ofReal (1 - δ) * V ≤ I := by
    calc ENNReal.ofReal (1 - δ) * V = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin (dimL ε))) ρ, ENNReal.ofReal (1 - δ) :=
          (setLIntegral_const _ _).symm
      _ ≤ I := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbound x hx)).1])
  have hIfin : I ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hup
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  have hupR : I.toReal ≤ (1 + δ) * V.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hloR : (1 - δ) * V.toReal ≤ I.toReal := by
    have := ENNReal.toReal_mono hIfin hlo
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hratio : ratioAt ε ρ = c * I.toReal / V.toReal := by
    unfold ratioAt
    rw [hb ρ hρ0 hρr, volume_ball_gLie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    rfl
  rw [Real.dist_eq, hratio]
  have key : |c * I.toReal / V.toReal - c| ≤ c * δ := by
    rw [abs_le]
    constructor
    · have : c * ((1 - δ) * V.toReal) ≤ c * I.toReal := mul_le_mul_of_nonneg_left hloR hc.le
      rw [le_sub_iff_add_le, le_div_iff₀ hVr]
      nlinarith
    · have : c * I.toReal ≤ c * ((1 + δ) * V.toReal) := mul_le_mul_of_nonneg_left hupR hc.le
      rw [sub_le_iff_le_add, div_le_iff₀ hVr]
      nlinarith
  exact lt_of_le_of_lt key hδe

theorem densOfBall (ε : Fin n → Bool) : DensOfBall ε := by
  rintro ⟨c, hc, s, hs, hb⟩
  have ht := tendsto_ratioAt_of_ball hc hs hb
  have he := gaugeU_eq ht
  exact ⟨he ▸ ht, he ▸ hc⟩

end Formalism.MainNotions.S.Gauge

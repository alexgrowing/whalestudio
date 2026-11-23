import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

abbrev dG (k r : ℕ) : ℕ := Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r)))

theorem gVol_mul (k r : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    gVol k r (a * s) = a ^ dG k r * gVol k r s := by
  unfold gVol
  rw [Measure.addHaar_ball_mul_of_pos volume _ ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem gVol_pos (k r : ℕ) {s : ℝ} (hs : 0 < s) : 0 < gVol k r s := by
  unfold gVol
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne

theorem rhs_bounds (hW : Sandwich) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      Vol k r μb ((1 - ε) * ρ) ≤ rhs k r μb ((wBall k r ρ).indicator 1) ∧
      rhs k r μb ((wBall k r ρ).indicator 1) ≤ Vol k r μb ((1 + ε) * ρ) := by
  obtain ⟨δ, hδ, hW'⟩ := hW k r ε hε0 hε1
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hN : ∀ᵐ x ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1), Matrix.of x ∈ Nset k r :=
    ae_iff.2 (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
  have hB : ∀ᵐ x ∂μb, Matrix.of x ∈ Formalism.FourierDecayAlt.B2.UWb k r := ae_iff.2 hμb.1.2.2.1
  constructor
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    split_ifs with hQ
    · have hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
          wBall k r ρ := (hW' ρ hρ hρδ n c m n' hn hm hn').2 hQ
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply]
    · exact zero_le
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    by_cases hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
        wBall k r ρ
    · have hQ := (hW' ρ hρ hρδ n c m n' hn hm hn').1 hx
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply, if_pos hQ]
    · rw [Set.indicator_apply, if_neg hx]
      exact zero_le

theorem scale_lim (hV : VolLim) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ρ : ℝ => (Vol k r μb (a * ρ)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 (((2 : ℝ) ^ r)⁻¹ * a ^ dG k r)) := by
  have hsc : Tendsto (fun ρ : ℝ => a * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact mul_pos ha hρ
  have h1 := ((hV k r μb hμb).comp hsc).mul_const (a ^ dG k r)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hg := gVol_pos k r (s := ρ) hρ
  have ha' : a ^ dG k r ≠ 0 := pow_ne_zero _ ha.ne'
  simp only [Function.comp]
  rw [gVol_mul k r ha ρ]
  field_simp

theorem rhsLim_of (hW : Sandwich) (hV : VolLim) : RhsLim := by
  intro k r μb hμb
  set L : ℝ := ((2 : ℝ) ^ r)⁻¹ with hLdef
  have hL : 0 < L := by positivity

  have hfin : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), rhs k r μb ((wBall k r ρ).indicator 1) ≠ ∞ := by
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := 1 / 2) (by norm_num) (by norm_num)
    have h := scale_lim hV k r μb hμb (a := 1 + 1 / 2) (by norm_num)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h1 h2 h3
    have hg := gVol_pos k r (s := ρ) h2
    have h4 : 0 < (Vol k r μb ((1 + 1 / 2) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + 1 / 2) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    exact ne_top_of_le_ne_top (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h2 h3).2
  rw [tendsto_order]
  constructor
  · intro a haL
    have hc : Tendsto (fun ε : ℝ => L * (1 - ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 - ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).1 a haL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 - ε) (by linarith)
    have hlo := (tendsto_order.1 h).1 a (by simpa [mul_comm] using h1)
    filter_upwards [hlo, hfin, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h4 h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    refine lt_of_lt_of_le h3 (div_le_div_of_nonneg_right ?_ hg.le)
    exact ENNReal.toReal_mono h4 (hb ρ h5 h6).1
  · intro b hbL
    have hc : Tendsto (fun ε : ℝ => L * (1 + ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 + ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).2 b hbL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 + ε) (by linarith)
    have hup := (tendsto_order.1 h).2 b (by simpa [mul_comm] using h1)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hup, hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h3' h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    have h4 : 0 < (Vol k r μb ((1 + ε) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + ε) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hg.le) h3
    exact ENNReal.toReal_mono (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h5 h6).2

end Formalism.L2.SG.Pf.BH

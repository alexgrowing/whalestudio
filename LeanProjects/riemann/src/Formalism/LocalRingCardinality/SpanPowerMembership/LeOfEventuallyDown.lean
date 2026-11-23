import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def QInv (nu : Measure V) (ε δ : ℝ) : Prop :=
  ∀ X : V, ‖X‖ < δ → ∀ r, 0 < r → r < δ →
    nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) ∧
      nu (closedBall 0 r) ≤ nu (closedBall X ((1 + ε) * r))

theorem tendsto_mul_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact mul_pos ht hr

variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

private theorem frequently_filterAt_of_eventually_closedBall (μ : Measure V) [SFinite μ] (x : V) {P : Set V → Prop}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (closedBall x r)) :
    ∃ᶠ a in (Besicovitch.vitaliFamily μ).filterAt x, P a := by
  intro hne
  have h2 := (Besicovitch.tendsto_filterAt μ x).eventually hne
  obtain ⟨r, hr1, hr2⟩ := (h.and h2).exists
  exact hr2 hr1

theorem le_of_eventually_up {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have ha : 0 < 1 - ε := by linarith
  have key : nu s ≤ (M' • lam) s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily nu) (M' • lam)
      MeasureTheory.Measure.AbsolutelyContinuous.rfl s fun x hx => frequently_filterAt_of_eventually_closedBall nu x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr ha)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 - ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 - ε)⁻¹ * ρ := mul_pos (inv_pos.mpr ha) h3
    have hq' := (hq x hx' _ hr h2).1
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x ha.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc nu (closedBall x ρ) ≤ nu (closedBall 0 ((1 - ε)⁻¹ * ρ)) := hq'
      _ ≤ M * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) := h1
      _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) :=
          by gcongr
      _ = M' * lam (closedBall x ρ) := by rw [e, mul_assoc]
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using key

theorem le_of_eventually_down {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have hb : 0 < 1 + ε := by linarith
  have key : ((M' : ℝ≥0∞) • lam) s ≤ nu s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily lam) nu
      (Measure.smul_absolutelyContinuous) s fun x hx => frequently_filterAt_of_eventually_closedBall lam x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr hb)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 + ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 + ε)⁻¹ * ρ := mul_pos (inv_pos.mpr hb) h3
    have hq' := (hq x hx' _ hr h2).2
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x hb.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at e
    simp only [Measure.smul_apply, smul_eq_mul]
    calc (M' : ℝ≥0∞) * lam (closedBall x ρ)
        = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by
          rw [e, mul_assoc]
      _ ≤ M * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by gcongr
      _ ≤ nu (closedBall 0 ((1 + ε)⁻¹ * ρ)) := h1
      _ ≤ nu (closedBall x ρ) := hq'
  simpa only [Measure.smul_apply, smul_eq_mul] using key

theorem tendsto_ofReal_pow (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun ε : ℝ => (1 + σ * ε) ^ n) (𝓝 0) (𝓝 ((1 + σ * 0) ^ n)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).pow n)
  rw [mul_zero, add_zero, one_pow] at h
  have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h
  rw [ENNReal.ofReal_one] at h2
  exact h2.mono_left nhdsWithin_le_nhds

theorem limsup_liminf_bounds {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := Besicovitch.ae_tendsto_rnDeriv nu lam
  have hfin := Measure.rnDeriv_lt_top nu lam
  have hpos : lam (ball (0 : V) δ) ≠ 0 := (measure_ball_pos lam 0 hδ).ne'
  obtain ⟨X, hX, hXt, hXf⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    apply hpos
    have h3 := ae_iff.mp (hae.and hfin)
    refine measure_mono_null (fun y hy => ?_) h3
    show ¬ _
    exact fun h => hcon ⟨y, hy, h.1, h.2⟩
  have hXn : ‖X‖ < δ := mem_ball_zero_iff.mp hX
  have key : ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r →
      nu (closedBall X (t * r)) / lam (closedBall 0 r) =
        ENNReal.ofReal (t ^ finrank ℝ V) * (nu (closedBall X (t * r)) / lam (closedBall X (t * r))) := by
    intro t ht r hr
    rw [Measure.addHaar_closedBall_mul lam X ht.le hr.le, ← mul_div_assoc, ENNReal.mul_div_mul_left]
    · exact (ENNReal.ofReal_pos.mpr (pow_pos ht _)).ne'
    · exact ENNReal.ofReal_ne_top
  have hup : Tendsto (fun r => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hlo : Tendsto (fun r => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r h0 h1
    exact ⟨h0, h1⟩
  refine ⟨nu.rnDeriv lam X, hXf.ne, ?_, ?_⟩
  · refine (Filter.limsup_le_limsup ?_).trans hup.limsup_eq.le
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · refine hlo.liminf_eq.ge.trans (Filter.liminf_le_liminf ?_)
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _

theorem exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  have hlam0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 :=
    fun r hr => (Metric.measure_closedBall_pos lam 0 hr).ne'
  have hlamT : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ :=
    fun r => (isCompact_closedBall (0 : V) r).measure_lt_top.ne
  have hcmp : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    intro ε h0 h1
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    obtain ⟨L, -, hls, hli⟩ := limsup_liminf_bounds lam nu h0 h1 hδ hqδ
    calc ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))
        ≤ ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by gcongr
  have hls_le : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    have A := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inl one_ne_zero) (b := limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    have B := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inl one_ne_zero) (b := liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    rw [one_mul] at A B
    refine le_of_tendsto_of_tendsto A B ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε h0 h1
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring, show (1 : ℝ) + 1 * ε = 1 + ε by ring]
    exact hcmp ε h0 h1
  have heq : liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) = limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := le_antisymm Filter.liminf_le_limsup hls_le
  have hlsT : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ⊤ := by
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, hls, -⟩ := limsup_liminf_bounds lam nu (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hδ hqδ
    exact lt_of_le_of_lt hls (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL).lt_top
  have hup : ∀ C : ℝ≥0, limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C * ENNReal.ofReal ((1 + -1 * ε) ^ finrank ℝ V)) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (lt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu h1 hqδ _ C hMe.le ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (C * ENNReal.ofReal ((1 + 1 * ε) ^ finrank ℝ V) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (gt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [one_mul] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_lt_liminf hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu h0 hqδ _ C hMe.ge ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hc0 : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≠ 0 := by
    intro hzero
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hB : closedBall (0 : V) (δ / 2) ⊆ ball 0 δ := closedBall_subset_ball (by linarith)
    obtain ⟨C, hC0, hClt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (hlamT (δ / 2)) (hpos (δ / 2) (by linarith)).ne'
    have hMe : ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) =
        C * ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hzero, hMe]
      exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hC0.ne')
        (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    have hle := le_of_eventually_up lam nu (by norm_num : (1 / 2 : ℝ) < 1) hqδ _ C hMe.le (by
      filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
      exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le) _ hB
    exact absurd hle (not_le.mpr hClt)
  refine ⟨limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)), hc0, hlsT.ne, hup, fun C hC => hdown C ?_⟩
  rw [heq]
  exact hC

theorem tendsto_ratio {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨C, haC, hCc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
    obtain ⟨δ, hδ, hd⟩ := hdown C hCc
    filter_upwards [hS δ hδ, hS0] with r hr h0
    refine lt_of_lt_of_le haC ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0.1) (Or.inl h0.2)]
    exact hd (S r) hr
  · obtain ⟨C, hcC, hCb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
    obtain ⟨δ, hδ, hu⟩ := hup C hcC
    filter_upwards [hS δ hδ] with r hr
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul (hu (S r) hr)) hCb

end Formalism.BasicNotions.Examples₂.CD

import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

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
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ht hr

variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

theorem le_of_eventually_up {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have key := (Besicovitch.vitaliFamily nu).measure_le_of_frequently_le (M' • lam)
    (Measure.AbsolutelyContinuous.refl nu) s ?_
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at key
    exact key
  intro X hX
  have hXn : ‖X‖ < δ := by simpa using hs hX
  have ht : Tendsto (fun r : ℝ => closedBall X ((1 - ε) * r)) (𝓝[>] 0)
      ((Besicovitch.vitaliFamily nu).filterAt X) :=
    (Besicovitch.tendsto_filterAt nu X).comp (tendsto_mul_pos (by linarith))
  refine ht.frequently (Eventually.frequently ?_)
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hXn
  filter_upwards [hev, Ioo_mem_nhdsGT hδ] with r hr hrδ
  calc nu (closedBall X ((1 - ε) * r)) ≤ nu (closedBall 0 r) := (hq X hXn r hrδ.1 hrδ.2).1
    _ ≤ M * lam (closedBall 0 r) := hr
    _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 r) := by gcongr
    _ = (M' • lam) (closedBall X ((1 - ε) * r)) := by
        rw [Measure.smul_apply, Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r,
          ENNReal.smul_def, smul_eq_mul, mul_assoc]

theorem le_of_eventually_down {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have key := (Besicovitch.vitaliFamily lam).measure_le_of_frequently_le (ρ := M' • lam) nu
    (Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl lam) M') s ?_
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at key
    exact key
  intro X hX
  have hXn : ‖X‖ < δ := by simpa using hs hX
  have ht : Tendsto (fun r : ℝ => closedBall X ((1 + ε) * r)) (𝓝[>] 0)
      ((Besicovitch.vitaliFamily lam).filterAt X) :=
    (Besicovitch.tendsto_filterAt lam X).comp (tendsto_mul_pos (by linarith))
  refine ht.frequently (Eventually.frequently ?_)
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hXn
  filter_upwards [hev, Ioo_mem_nhdsGT hδ] with r hr hrδ
  calc (M' • lam) (closedBall X ((1 + ε) * r))
      = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 r) := by
        rw [Measure.smul_apply, Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r,
          ENNReal.smul_def, smul_eq_mul, mul_assoc]
    _ ≤ M * lam (closedBall 0 r) := by gcongr
    _ ≤ nu (closedBall 0 r) := hr
    _ ≤ nu (closedBall X ((1 + ε) * r)) := (hq X hXn r hrδ.1 hrδ.2).2

theorem tendsto_ofReal_pow (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have := h.tendsto 0
  simp only [mul_zero, add_zero, one_pow, ENNReal.ofReal_one] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem limsup_liminf_bounds {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := (Besicovitch.ae_tendsto_rnDeriv nu lam).and (Measure.rnDeriv_lt_top nu lam)
  obtain ⟨X, hXm, hX, hXfin⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    push Not at hcon
    have hsub : ball (0 : V) δ ⊆ {X | ¬ (Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r))
        (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧ nu.rnDeriv lam X < ⊤)} := by
      intro X hX h
      exact absurd h.2 (not_lt.mpr (hcon X hX h.1))
    have h0 := measure_mono_null hsub (ae_iff.mp hae)
    exact (measure_ball_pos lam (0 : V) hδ).ne' h0
  have hXn : ‖X‖ < δ := by simpa using hXm
  refine ⟨nu.rnDeriv lam X, hXfin.ne, ?_, ?_⟩
  · have hA0 : ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hA0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · have hB0 : ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have : 0 < 1 - ε := by linarith
      positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hB0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _

theorem exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  set f : ℝ → ℝ≥0∞ := fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r) with hf
  set n := finrank ℝ V with hn
  have hl0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 := fun r hr =>
    (measure_closedBall_pos lam 0 hr).ne'
  have hlt : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ := fun r => measure_closedBall_lt_top.ne
  set b := limsup f (𝓝[>] (0 : ℝ)) with hb
  set a := liminf f (𝓝[>] (0 : ℝ)) with ha
  have hI : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := Ioo_mem_nhdsGT one_pos
  have hbtop : b ≠ ⊤ := by
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, h1, -⟩ := limsup_liminf_bounds lam nu (by norm_num) (by norm_num) hδ hQ
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h1
  have hba : b ≤ a := by
    have h1 : Tendsto (fun ε : ℝ => b * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0) (𝓝 (b * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + 1 * ε) ^ n) * a) (𝓝[>] 0) (𝓝 (1 * a)) :=
      ENNReal.Tendsto.mul_const (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    rw [one_mul] at h2
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [hI] with ε hε
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε.1 hε.2
    obtain ⟨L, hL, h3, h4⟩ := limsup_liminf_bounds lam nu hε.1 hε.2 hδ hQ
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    have e2 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1, e2]
    calc b * ENNReal.ofReal ((1 - ε) ^ n)
        ≤ (ENNReal.ofReal ((1 + ε) ^ n) * L) * ENNReal.ofReal ((1 - ε) ^ n) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal ((1 - ε) ^ n) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ n) * a := by gcongr
  have hft : Tendsto f (𝓝[>] 0) (𝓝 b) := tendsto_of_le_liminf_of_limsup_le hba le_rfl
  have hup : ∀ M : ℝ≥0, b < M → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      nu (closedBall (0 : V) r) ≤ M * lam (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (gt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff (hl0 r hr0) (hlt r)).mp hr.le
  have hdown : ∀ M : ℝ≥0, (M : ℝ≥0∞) < b → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      M * lam (closedBall (0 : V) r) ≤ nu (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (lt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hl0 r hr0)) (Or.inl (hlt r))).mp hr.le
  refine ⟨b, ?_, hbtop, ?_, ?_⟩
  · intro hb0
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hz : nu (ball (0 : V) δ) = 0 := by
      by_contra hne
      have hlb : lam (ball (0 : V) δ) ≠ ⊤ := measure_ball_lt_top.ne
      have hpos' : 0 < nu (ball (0 : V) δ) / lam (ball (0 : V) δ) :=
        ENNReal.div_pos hne hlb
      obtain ⟨M', hM'0, hM'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos'
      have hM'pos : 0 < M' := by exact_mod_cast hM'0
      have hlt' := ENNReal.mul_lt_of_lt_div hM'
      have hkpos : 0 < Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n) := by
        rw [Real.toNNReal_pos]; positivity
      have := le_of_eventually_up lam nu (ε := 1 / 2) (by norm_num) hQ
        (M' * Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n)) M'
        (by rw [ENNReal.coe_mul]; rfl)
        (hup _ (by rw [hb0]; exact_mod_cast mul_pos hM'pos hkpos)) (ball 0 δ) subset_rfl
      exact absurd hlt' (not_lt.mpr this)
    have h1 := hpos (δ / 2) (by linarith)
    have h2 : nu (closedBall (0 : V) (δ / 2)) ≤ nu (ball (0 : V) δ) :=
      measure_mono (closedBall_subset_ball (by linarith))
    rw [hz] at h2
    exact absurd h1 (not_lt.mpr h2)
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (lt_mem_nhds hC'2)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu hε01.2 hQ C' C hε.le (hup C' hC'1) s hs⟩
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + 1 * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (gt_mem_nhds hC'1)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu hε01.1 hQ C' C hε.le (hdown C' hC'2) s hs⟩

theorem tendsto_ratio {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hdown C' hC'2
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_lt_of_le hC'1 ((ENNReal.le_div_iff_mul_le (Or.inl hr0.1) (Or.inl hr0.2)).mpr (h _ hr))
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hup C' hC'1
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_le_of_lt ((ENNReal.div_le_iff hr0.1 hr0.2).mpr (h _ hr)) hC'2

end ReciprocityTheory.ChartRestriction.DS.HExp

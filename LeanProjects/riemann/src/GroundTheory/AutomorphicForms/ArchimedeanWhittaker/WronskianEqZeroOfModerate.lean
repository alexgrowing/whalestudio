import Mathlib

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set

theorem exp_growth_false {A b K Y : ℝ} {M : ℕ} (hA : 0 < A) (hb : 0 < b)
    (h : ∀ y ≥ Y, A * Real.exp (b * y) ≤ K * y ^ M) : False := by
  have ht : Tendsto (fun y => Real.exp (b * y) / (b * y) ^ M) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop M).comp (tendsto_id.const_mul_atTop hb)
  have hbM : 0 < A * b ^ M := mul_pos hA (pow_pos hb M)
  obtain ⟨y, hy1, hy2, hy3⟩ := ((ht.eventually_ge_atTop (K / (A * b ^ M) + 1)).and
    ((eventually_ge_atTop Y).and (eventually_gt_atTop 0))).exists
  have hpos : 0 < (b * y) ^ M := pow_pos (mul_pos hb hy3) M
  have h1 : (K / (A * b ^ M) + 1) * (b * y) ^ M ≤ Real.exp (b * y) := by
    rwa [le_div_iff₀ hpos] at hy1
  have h2 := h y hy2
  have hyM : 0 < y ^ M := pow_pos hy3 M
  have e : A * ((K / (A * b ^ M) + 1) * (b * y) ^ M) = K * y ^ M + A * b ^ M * y ^ M := by
    rw [mul_pow]; field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hA.le
  rw [e] at h3
  nlinarith [mul_pos hbM hyM]

theorem inner_mul_self (z q : ℂ) : inner ℝ z (q * z) = q.re * ‖z‖ ^ 2 := by
  rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set

theorem monotoneOn_Ici_of_hasDerivAt {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hpos : ∀ y ≥ a, 0 ≤ u' y) : MonotoneOn u (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := u') (convex_Ici a)
    (fun y hy => (hu y hy).continuousAt.continuousWithinAt) (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ici] at hy
    exact (hu y (le_of_lt hy)).hasDerivWithinAt
  · rw [interior_Ici] at hy
    exact hpos y (le_of_lt hy)

theorem antitoneOn_Ici_of_hasDerivAt {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hneg : ∀ y ≥ a, u' y ≤ 0) : AntitoneOn u (Ici a) := by
  have := monotoneOn_Ici_of_hasDerivAt (u := fun y => -u y) (u' := fun y => -u' y)
    (fun y hy => (hu y hy).neg) (fun y hy => neg_nonneg.2 (hneg y hy))
  intro x hx y hy hxy
  have := this hx hy hxy
  simpa using this

theorem tendsto_zero_of_moderate {q f f' : ℝ → ℂ} {Y₀ c C : ℝ} {N : ℕ} (hc : 0 < c)
    (hq : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hgr : ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N) : Tendsto f atTop (𝓝 0) := by
  set u : ℝ → ℝ := fun y => ‖f y‖ ^ 2 with hudef
  set u1 : ℝ → ℝ := fun y => 2 * inner ℝ (f y) (f' y) with hu1def
  set w : ℝ → ℝ := fun y => 2 * (inner ℝ (f y) (q y * f y) + inner ℝ (f' y) (f' y)) with hwdef
  have hu : ∀ y ≥ Y₀, HasDerivAt u (u1 y) y := fun y hy => (hf y hy).norm_sq
  have hu1 : ∀ y ≥ Y₀, HasDerivAt u1 (w y) y := fun y hy =>
    ((hf y hy).inner ℝ (hf' y hy)).const_mul 2
  have hw : ∀ y ≥ Y₀, 2 * c ^ 2 * u y ≤ w y := by
    intro y hy
    simp only [hwdef, hudef, inner_mul_self, real_inner_self_eq_norm_sq]
    have := hq y hy
    nlinarith [sq_nonneg ‖f y‖, sq_nonneg ‖f' y‖]
  have hu0 : ∀ y, 0 ≤ u y := fun y => sq_nonneg _
  have hwpos : ∀ y ≥ Y₀, 0 ≤ w y := fun y hy =>
    le_trans (mul_nonneg (by positivity) (hu0 y)) (hw y hy)

  have hug : ∀ y ≥ max Y₀ 0, u y ≤ C ^ 2 * y ^ (2 * N) := by
    intro y hy
    have h1 := hgr y (le_trans (le_max_left _ _) hy)
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    calc u y = ‖f y‖ ^ 2 := rfl
      _ ≤ (C * y ^ N) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = C ^ 2 * y ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]
  by_cases hpos : ∃ y₁ ≥ Y₀, 0 < u1 y₁
  · exfalso
    obtain ⟨y₁, hy₁, hpos₁⟩ := hpos
    have hmono1 : MonotoneOn u1 (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
      (fun y hy => hu1 y (le_trans hy₁ hy)) (fun y hy => hwpos y (le_trans hy₁ hy))
    have hu1ge : ∀ y ≥ y₁, u1 y₁ ≤ u1 y := fun y hy => hmono1 (mem_Ici.2 le_rfl) hy hy

    have hlin : ∀ y ≥ y₁, u y₁ + u1 y₁ * (y - y₁) ≤ u y := by
      have hm : MonotoneOn (fun y => u y - u1 y₁ * y) (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
        (fun y hy => ((hu y (le_trans hy₁ hy)).sub ((hasDerivAt_id y).const_mul (u1 y₁))))
        (fun y hy => by simpa using hu1ge y hy)
      intro y hy
      have := hm (mem_Ici.2 le_rfl) hy hy
      linarith

    have hQ : MonotoneOn (fun y => u1 y ^ 2 - 2 * c ^ 2 * u y ^ 2) (Ici y₁) := by
      refine monotoneOn_Ici_of_hasDerivAt
        (u' := fun y => 2 * u1 y * w y - 2 * c ^ 2 * (2 * u y * u1 y))
        (fun y hy => ?_) (fun y hy => ?_)
      · have h3 := ((hu1 y (le_trans hy₁ hy)).pow 2).sub
          (((hu y (le_trans hy₁ hy)).pow 2).const_mul (2 * c ^ 2))
        refine h3.congr_deriv ?_
        push_cast
        ring
      · have h1 : 0 ≤ u1 y := le_trans hpos₁.le (hu1ge y hy)
        have h2 := hw y (le_trans hy₁ hy)
        nlinarith [mul_nonneg h1 (sub_nonneg.2 h2)]
    set K₀ := u1 y₁ ^ 2 - 2 * c ^ 2 * u y₁ ^ 2 with hK₀
    have hQge : ∀ y ≥ y₁, K₀ ≤ u1 y ^ 2 - 2 * c ^ 2 * u y ^ 2 := fun y hy =>
      hQ (mem_Ici.2 le_rfl) hy hy
    set y₂ := y₁ + (|K₀| + 1) / (c * u1 y₁) with hy₂def
    have hy₂ : y₁ ≤ y₂ := by
      rw [hy₂def]; have : 0 ≤ (|K₀| + 1) / (c * u1 y₁) := by positivity
      linarith
    have hmonou : MonotoneOn u (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
      (fun y hy => hu y (le_trans hy₁ hy)) (fun y hy => le_trans hpos₁.le (hu1ge y hy))
    have hcu₂ : |K₀| + 1 ≤ c * u y₂ := by
      have := hlin y₂ hy₂
      have e : u1 y₁ * (y₂ - y₁) = (|K₀| + 1) / c := by
        rw [hy₂def]; field_simp; ring
      have hu1 : 0 ≤ u y₁ := hu0 y₁
      rw [e] at this
      have : (|K₀| + 1) / c ≤ u y₂ := by linarith
      rwa [div_le_iff₀ hc, mul_comm] at this
    have hcu : ∀ y ≥ y₂, |K₀| + 1 ≤ c * u y := fun y hy =>
      le_trans hcu₂ (mul_le_mul_of_nonneg_left
        (hmonou (mem_Ici.2 hy₂) (mem_Ici.2 (le_trans hy₂ hy)) hy) hc.le)
    have hu1cu : ∀ y ≥ y₂, c * u y ≤ u1 y := by
      intro y hy
      have h1 := hQge y (le_trans hy₂ hy)
      have h2 := hcu y hy
      have h3 : 0 ≤ u1 y := le_trans hpos₁.le (hu1ge y (le_trans hy₂ hy))
      have h4 : 0 ≤ c * u y := le_trans (by positivity) h2
      have h5 : (c * u y) ^ 2 ≤ u1 y ^ 2 := by
        have : |K₀| ≤ (c * u y) ^ 2 := by nlinarith [abs_nonneg K₀]
        nlinarith [neg_abs_le K₀]
      exact (pow_le_pow_iff_left₀ h4 h3 (by norm_num : (2 : ℕ) ≠ 0)).1 h5

    have hE : MonotoneOn (fun y => u y * Real.exp (-(c * y))) (Ici y₂) := by
      refine monotoneOn_Ici_of_hasDerivAt
        (u' := fun y => u1 y * Real.exp (-(c * y)) + u y * (Real.exp (-(c * y)) * -(c * 1)))
        (fun y hy => ?_) (fun y hy => ?_)
      · exact (hu y (le_trans hy₁ (le_trans hy₂ hy))).mul
          (((hasDerivAt_id y).const_mul c).neg.exp)
      · have := hu1cu y hy
        have he := Real.exp_pos (-(c * y))
        nlinarith
    have hu₂pos : 0 < u y₂ := by
      have : 0 < c * u y₂ := lt_of_lt_of_le (by positivity) hcu₂
      exact pos_of_mul_pos_right this hc.le
    refine exp_growth_false (A := u y₂ * Real.exp (-(c * y₂))) (b := c) (K := C ^ 2)
      (M := 2 * N) (Y := max y₂ (max Y₀ 0)) (mul_pos hu₂pos (Real.exp_pos _)) hc fun y hy => ?_
    have hy2 : y₂ ≤ y := le_trans (le_max_left _ _) hy
    have h1 := hE (mem_Ici.2 le_rfl) (mem_Ici.2 hy2) hy2
    simp only at h1
    have h2 := hug y (le_trans (le_max_right _ _) hy)
    have e : u y * Real.exp (-(c * y)) * Real.exp (c * y) = u y := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    calc u y₂ * Real.exp (-(c * y₂)) * Real.exp (c * y)
        ≤ u y * Real.exp (-(c * y)) * Real.exp (c * y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = u y := e
      _ ≤ C ^ 2 * y ^ (2 * N) := h2
  · push Not at hpos
    have hanti : AntitoneOn u (Ici Y₀) := antitoneOn_Ici_of_hasDerivAt hu hpos

    have hu_lim : Tendsto u atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      by_cases hex : ∃ y₀ ≥ Y₀, u y₀ < ε
      · obtain ⟨y₀, hy₀, hlt⟩ := hex
        refine ⟨y₀, fun y hy => ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu0 y)]
        exact lt_of_le_of_lt (hanti (mem_Ici.2 hy₀) (mem_Ici.2 (le_trans hy₀ hy)) hy) hlt
      · exfalso
        push Not at hex
        have hm : MonotoneOn (fun y => u1 y - 2 * c ^ 2 * ε * y) (Ici Y₀) :=
          monotoneOn_Ici_of_hasDerivAt (u' := fun y => w y - 2 * c ^ 2 * ε * 1)
            (fun y hy => (hu1 y hy).sub ((hasDerivAt_id y).const_mul _))
            (fun y hy => by
              have h1 := hw y hy
              have h2 := hex y hy
              have : 2 * c ^ 2 * ε ≤ 2 * c ^ 2 * u y :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              linarith)
        set y₃ := Y₀ + (|u1 Y₀| + 1) / (2 * c ^ 2 * ε) with hy₃
        have hy₃ge : Y₀ ≤ y₃ := by
          rw [hy₃]; have : 0 ≤ (|u1 Y₀| + 1) / (2 * c ^ 2 * ε) := by positivity
          linarith
        have h1 := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hy₃ge) hy₃ge
        simp only at h1
        have h2 := hpos y₃ hy₃ge
        have e : 2 * c ^ 2 * ε * (y₃ - Y₀) = |u1 Y₀| + 1 := by
          rw [hy₃]; field_simp; ring
        nlinarith [le_abs_self (u1 Y₀), neg_abs_le (u1 Y₀)]
    have : Tendsto (fun y => ‖f y‖) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hu_lim
      simp only [Function.comp_def, Real.sqrt_zero] at h
      refine h.congr fun y => ?_
      simp [hudef, Real.sqrt_sq (norm_nonneg _)]
    exact tendsto_zero_iff_norm_tendsto_zero.2 this

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set

theorem tendsto_deriv_zero {q f f' : ℝ → ℂ} {Y₀ M : ℝ} (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hlim : Tendsto f atTop (𝓝 0)) : Tendsto f' atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  set δ := ε / (3 + |M|) with hδ
  have hδpos : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Y₁, hY₁⟩ := hlim δ hδpos
  refine ⟨max Y₀ Y₁, fun y hy => ?_⟩
  have hyY₀ : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hyY₁ : Y₁ ≤ y := le_trans (le_max_right _ _) hy
  have hfδ : ∀ s ≥ y, ‖f s‖ < δ := fun s hs => by
    have := hY₁ s (le_trans hyY₁ hs); rwa [dist_zero_right] at this

  have h1 : ∀ t ∈ Icc y (y + 1), ‖f' t - f' y‖ ≤ |M| * δ * (t - y) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun t => q t * f t)
      (fun t ht => (hf' t (le_trans hyY₀ ht.1)).hasDerivWithinAt) (fun t ht => ?_)
    rw [norm_mul]
    exact mul_le_mul (le_trans (hqM t (le_trans hyY₀ ht.1)) (le_abs_self M))
      (hfδ t ht.1).le (norm_nonneg _) (abs_nonneg M)

  have h2 : ‖(f (y + 1) - (y + 1) • f' y) - (f y - y • f' y)‖ ≤ |M| * δ * ((y + 1) - y) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => f t - t • f' y)
      (f' := fun t => f' t - f' y) (fun t ht => ?_) (fun t ht => ?_) (y + 1)
      ⟨by linarith, le_rfl⟩
    · have := ((hf t (le_trans hyY₀ ht.1)).sub ((hasDerivAt_id t).smul_const (f' y)))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · refine le_trans (h1 t (Ico_subset_Icc_self ht)) ?_
      calc |M| * δ * (t - y) ≤ |M| * δ * ((y + 1) - y) :=
            mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
        _ = |M| * δ := by ring
  have e : (f (y + 1) - (y + 1) • f' y) - (f y - y • f' y) = f (y + 1) - f y - f' y := by
    rw [add_smul, one_smul]; abel
  rw [e, add_sub_cancel_left, mul_one] at h2
  rw [dist_zero_right]
  have h3 : ‖f' y‖ ≤ ‖f (y + 1)‖ + ‖f y‖ + |M| * δ := by
    have : f' y = f (y + 1) - f y - (f (y + 1) - f y - f' y) := by abel
    rw [this]
    refine le_trans (norm_sub_le _ _) (add_le_add (norm_sub_le _ _) h2)
  have h4 : ‖f (y + 1)‖ + ‖f y‖ + |M| * δ < (3 + |M|) * δ := by
    have := hfδ (y + 1) (by linarith)
    have := hfδ y le_rfl
    nlinarith [abs_nonneg M]
  have h5 : (3 + |M|) * δ = ε := by rw [hδ]; field_simp
  linarith

theorem wronskian_eq_zero {q f f' g g' : ℝ → ℂ}
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (hg : ∀ y > 0, HasDerivAt g (g' y) y) (hg' : ∀ y > 0, HasDerivAt g' (q y * g y) y)
    (hf0 : Tendsto f atTop (𝓝 0)) (hf0' : Tendsto f' atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0)) (hg0' : Tendsto g' atTop (𝓝 0)) :
    ∀ y > 0, f y * g' y - f' y * g y = 0 := by
  set W : ℝ → ℂ := fun y => f y * g' y - f' y * g y with hW
  have hWd : ∀ y > 0, HasDerivAt W 0 y := by
    intro y hy
    have := ((hf y hy).mul (hg' y hy)).sub ((hf' y hy).mul (hg y hy))
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ y > 0, W y = W 1 := by
    intro y hy
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hWd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hWd z hz).deriv) hy (mem_Ioi.2 one_pos)
  have hlim : Tendsto W atTop (𝓝 0) := by
    have := (hf0.mul hg0').sub (hf0'.mul hg0)
    simpa using this
  have hlim' : Tendsto W atTop (𝓝 (W 1)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact (hconst y hy).symm)
  have h1 : W 1 = 0 := tendsto_nhds_unique hlim' hlim
  intro y hy
  show W y = 0
  rw [hconst y hy, h1]

theorem eq_zero_of_ode {q f f' : ℝ → ℂ} (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (h1 : f 1 = 0) (h1' : f' 1 = 0) : ∀ y > 0, f y = 0 := by
  intro y hy
  set a := min y 1 / 2 with ha
  set b := max y 1 + 1 with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : Icc a b ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha0 ht.1
  obtain ⟨M, hM⟩ := (isCompact_Icc.exists_bound_of_continuousOn (hq.mono hab))
  set K : NNReal := ⟨1 + |M|, by positivity⟩ with hK
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t p => (p.2, q t * p.1) with hv
  have hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) univ := by
    intro t ht
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun p p' => ?_)
    have hqt : ‖q t‖ ≤ |M| := le_trans (hM t (Ioo_subset_Icc_self ht)) (le_abs_self M)
    simp only [hv, Prod.dist_eq, hK]
    refine max_le ?_ ?_
    · calc dist p.2 p'.2 ≤ max (dist p.1 p'.1) (dist p.2 p'.2) := le_max_right _ _
        _ ≤ (1 + |M|) * max (dist p.1 p'.1) (dist p.2 p'.2) := by
          nlinarith [abs_nonneg M, le_max_right (dist p.1 p'.1) (dist p.2 p'.2), dist_nonneg (x := p.2) (y := p'.2)]
    · rw [dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
      calc ‖q t‖ * dist p.1 p'.1 ≤ |M| * max (dist p.1 p'.1) (dist p.2 p'.2) :=
            mul_le_mul hqt (le_max_left _ _) dist_nonneg (abs_nonneg M)
        _ ≤ (1 + |M|) * max (dist p.1 p'.1) (dist p.2 p'.2) := by
          nlinarith [le_max_left (dist p.1 p'.1) (dist p.2 p'.2), dist_nonneg (x := p.1) (y := p'.1)]
  have hsol : ∀ t ∈ Ioo a b, HasDerivAt (fun t => (f t, f' t)) (v t (f t, f' t)) t ∧
      (f t, f' t) ∈ (univ : Set (ℂ × ℂ)) := fun t ht =>
    ⟨(hf t (hab (Ioo_subset_Icc_self ht))).prodMk (hf' t (hab (Ioo_subset_Icc_self ht))), mem_univ _⟩
  have hzero : ∀ t ∈ Ioo a b, HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (v t (0, 0)) t ∧
      ((0 : ℂ), (0 : ℂ)) ∈ (univ : Set (ℂ × ℂ)) := fun t _ => by
    refine ⟨(hasDerivAt_const t ((0 : ℂ), (0 : ℂ))).congr_deriv ?_, mem_univ _⟩
    simp [hv]
    rfl
  have h1mem : (1 : ℝ) ∈ Ioo a b := by
    constructor
    · rw [ha]; have := min_le_right y 1; linarith
    · rw [hb]; have := le_max_right y 1; linarith
  have hymem : y ∈ Ioo a b := by
    constructor
    · rw [ha]; have := min_le_left y 1; linarith
    · rw [hb]; have := le_max_left y 1; linarith
  have := ODE_solution_unique_of_mem_Ioo (s := fun _ => univ) hlip h1mem hsol hzero
    (by simp [h1, h1']) hymem
  exact congrArg Prod.fst this

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set

theorem wronskian_eq_zero_of_moderate {q f f' g g' : ℝ → ℂ} {c M Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (hc : 0 < c) (hqre : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re) (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (hg : ∀ y > 0, HasDerivAt g (g' y) y) (hg' : ∀ y > 0, HasDerivAt g' (q y * g y) y)
    (hfgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N)
    (hggr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖g y‖ ≤ C * y ^ N) :
    f 1 * g' 1 - f' 1 * g 1 = 0 := by
  have pos : ∀ y ≥ Y₀, y > 0 := fun y hy => lt_of_lt_of_le hY₀ hy
  obtain ⟨Cf, Nf, hCf⟩ := hfgr
  obtain ⟨Cg, Ng, hCg⟩ := hggr
  have hf0 := tendsto_zero_of_moderate hc hqre (fun y hy => hf y (pos y hy))
    (fun y hy => hf' y (pos y hy)) hCf
  have hg0 := tendsto_zero_of_moderate hc hqre (fun y hy => hg y (pos y hy))
    (fun y hy => hg' y (pos y hy)) hCg
  have hf0' := tendsto_deriv_zero hqM (fun y hy => hf y (pos y hy)) (fun y hy => hf' y (pos y hy)) hf0
  have hg0' := tendsto_deriv_zero hqM (fun y hy => hg y (pos y hy)) (fun y hy => hg' y (pos y hy)) hg0
  exact wronskian_eq_zero hf hf' hg hg' hf0 hf0' hg0 hg0' 1 one_pos

theorem eq_zero_of_first_order {F : ℝ → ℂ} {m : ℤ} {b : ℝ} (hb : 0 < b)
    (hF : ∀ y > 0, HasDerivAt F ((((m : ℝ) / (2 * y) + b : ℝ) : ℂ) * F y) y)
    (hgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ 1, ‖F y‖ ≤ C * y ^ N) : ∀ y > 0, F y = 0 := by
  obtain ⟨C, N, hC⟩ := hgr
  set u : ℝ → ℝ := fun y => ‖F y‖ ^ 2 with hudef
  set V : ℝ → ℝ := fun y => u y * (y ^ (-m) * Real.exp (-(2 * b * y))) with hVdef
  have hu : ∀ y > 0, HasDerivAt u (2 * ((m : ℝ) / (2 * y) + b) * u y) y := by
    intro y hy
    have := (hF y hy).norm_sq
    refine this.congr_deriv ?_
    rw [inner_mul_self, Complex.ofReal_re]
    simp only [hudef]
    ring
  have hV : ∀ y > 0, HasDerivAt V 0 y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => y ^ (-m)) (((-m : ℤ) : ℝ) * y ^ (-m - 1)) y :=
      hasDerivAt_zpow (-m) y (Or.inl hy.ne')
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(2 * b * y)))
        (Real.exp (-(2 * b * y)) * -(2 * b * 1)) y :=
      ((hasDerivAt_id y).const_mul (2 * b)).neg.exp
    have := (hu y hy).mul (h1.mul h2)
    refine this.congr_deriv ?_
    have hy0 : y ≠ 0 := hy.ne'
    have e : y ^ (-m - 1) = y ^ (-m) / y := by
      rw [zpow_sub₀ hy0, zpow_one]
    simp only [Pi.mul_apply]
    rw [e]
    push_cast
    field_simp
    ring
  have hconst : ∀ y > 0, V y = V 1 := fun y hy =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hV z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hV z hz).deriv) hy (mem_Ioi.2 one_pos)
  have hV1 : 0 ≤ V 1 := by
    simp only [hVdef]; positivity
  have hV10 : V 1 = 0 := by
    by_contra hne
    have hV1pos : 0 < V 1 := lt_of_le_of_ne hV1 (Ne.symm hne)
    refine exp_growth_false (A := V 1) (b := 2 * b) (K := C ^ 2) (M := 2 * N + m.natAbs)
      (Y := 1) hV1pos (by positivity) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have h1 : u y * (y ^ (-m) * Real.exp (-(2 * b * y))) = V 1 := hconst y hy0
    have hu_le : u y ≤ C ^ 2 * y ^ (2 * N) := by
      have := hC y hy
      calc u y = ‖F y‖ ^ 2 := rfl
        _ ≤ (C * y ^ N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = C ^ 2 * y ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]
    have hpow : y ^ (-m) ≤ y ^ m.natAbs := by
      have : y ^ (-m) ≤ y ^ ((m.natAbs : ℤ)) := zpow_le_zpow_right₀ hy (by omega)
      rwa [zpow_natCast] at this
    have hexp : Real.exp (2 * b * y) * Real.exp (-(2 * b * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hC2 : 0 ≤ C ^ 2 * y ^ (2 * N) := le_trans (by positivity) hu_le
    calc V 1 * Real.exp (2 * b * y) = u y * y ^ (-m) := by
          rw [← h1]
          calc u y * (y ^ (-m) * Real.exp (-(2 * b * y))) * Real.exp (2 * b * y)
              = u y * y ^ (-m) * (Real.exp (2 * b * y) * Real.exp (-(2 * b * y))) := by ring
            _ = u y * y ^ (-m) := by rw [hexp, mul_one]
      _ ≤ C ^ 2 * y ^ (2 * N) * y ^ m.natAbs :=
          mul_le_mul hu_le hpow (zpow_nonneg hy0.le _) hC2
      _ = C ^ 2 * y ^ (2 * N + m.natAbs) := by rw [pow_add, mul_assoc]
  intro y hy
  have h1 := hconst y hy
  rw [hV10] at h1
  simp only [hVdef] at h1
  have hpos : 0 < y ^ (-m) * Real.exp (-(2 * b * y)) :=
    mul_pos (zpow_pos hy _) (Real.exp_pos _)
  have hu0 : u y = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hpos.ne'
  have : ‖F y‖ = 0 := by
    have : ‖F y‖ ^ 2 = 0 := hu0
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  exact norm_eq_zero.1 this

end GroundTheory.Automorphic.ArchWhittaker

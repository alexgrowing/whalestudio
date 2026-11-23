import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal

noncomputable section

def apraW (d : ℕ) (ε τ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  if t < ε then ENNReal.ofReal ((max (t ^ 2) τ) ^ (-(d : ℝ))) else 0

lemma apraW_meas (d : ℕ) (ε τ : ℝ) : Measurable (apraW d ε τ) := by
  unfold apraW
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp
    (((measurable_id.pow_const 2).max measurable_const).pow_const _)

lemma apraW_anti (d : ℕ) (ε : ℝ) {τ τ' : ℝ} (hτ : 0 < τ) (h : τ ≤ τ') (t : ℝ) :
    apraW d ε τ' t ≤ apraW d ε τ t := by
  unfold apraW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right hτ)
      (max_le_max le_rfl h) (neg_nonpos.mpr (Nat.cast_nonneg d)))
  · exact le_rfl

lemma apra_slice (d k : ℕ) (hMVd : MVStatement d) (ε τ : ℝ) (u : V d × V k → ℂ)
    (hu : DifferentiableOn ℂ u (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) (ζ : V k)
    (hζ : ζ ∈ ball (0 : V k) ε) :
    ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
      ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hdiff : DifferentiableOn ℂ (fun x : V d => u (x, ζ)) (ball 0 ε) :=
    hu.comp (differentiableOn_id.prodMk (differentiableOn_const ζ)) (fun x hx => ⟨hx, hζ⟩)
  have h := hMVd ε (fun x => u (x, ζ)) (apraW d ε τ) hdiff (apraW_meas d ε τ)
    (fun t ht => by simp [apraW, not_lt.mpr ht])
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x => ?_
  by_cases hx : ‖x‖ < ε
  · have hx' : x ∈ ball (0 : V d) ε := mem_ball_zero_iff.mpr hx
    simp only [apraW, if_pos hx, Set.indicator_of_mem hx']
    rw [ENNReal.ofReal_mul (by positivity)]
  · have hx' : x ∉ ball (0 : V d) ε := fun h => hx (mem_ball_zero_iff.mp h)
    simp [apraW, hx]

lemma apra_base (k : ℕ) (hMVk : MVStatement k) (ε : ℝ) (g : V k → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 ε)) :
    ENNReal.ofReal (‖g 0‖ ^ 2) * volume (ball (0 : V k) ε) ≤
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
  have h := hMVk ε g (fun t => if t < ε then 1 else 0) hg
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    (fun t ht => by simp [not_lt.mpr ht])
  have e1 : ∫⁻ y : V k, (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      volume (ball (0 : V k) ε) := by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  have e2 : ∫⁻ y : V k, ENNReal.ofReal (‖g y‖ ^ 2) *
      (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  rw [e1, e2] at h
  exact h

lemma apra_blow (d : ℕ) (hd : 1 ≤ d) (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) :
    ⨆ n : ℕ, ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
  have : Nontrivial (V d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set f : ℕ → V d → ℝ≥0∞ := fun n x => apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ with hf
  have hmeas : ∀ n, Measurable (f n) := fun n => (apraW_meas _ _ _).comp measurable_norm
  have hmono : Monotone f := by
    intro m n hmn x
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    show apraW d ε (1 / ((m : ℝ) + 1)) ‖x‖ ≤ apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖
    exact apraW_anti d ε h2 h1 _
  rw [← lintegral_iSup hmeas hmono]
  set g : V d → ℝ≥0∞ := fun x => ENNReal.ofReal ‖x‖ ^ (-2 * (d : ℝ)) with hg
  have hpt : ∀ x : V d, x ≠ 0 → (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    intro x hx0
    by_cases hx : ‖x‖ < ε
    · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hx)]
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pow_pos hpos 2)
      refine le_trans ?_ (le_iSup _ n)
      simp only [hf, hg, apraW, if_pos hx]
      rw [max_eq_left hn.le, ENNReal.ofReal_rpow_of_pos hpos, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      apply le_of_eq
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (mem_ball_zero_iff.mp h))]
      exact bot_le
  have hae : ∀ᵐ x ∂(volume : Measure (V d)), (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    have h0 : ∀ᵐ x ∂(volume : Measure (V d)), x ∉ ({0} : Set (V d)) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with x hx using hpt x (by simpa using hx)
  have hT : ∫⁻ y in ball (0 : V d) 1, g y = ⊤ :=
    not_lt_top_iff.mp (fun h => lt_irrefl _ ((hMVI hd d).1 h))
  have hdn : -2 * (d : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpt2 : ∀ y : V d, g y ≤ (ball (0 : V d) ε).indicator g y + ENNReal.ofReal ε ^ (-2 * (d : ℝ)) := by
    intro y
    by_cases hy : y ∈ ball (0 : V d) ε
    · rw [Set.indicator_of_mem hy]
      exact le_self_add
    · rw [Set.indicator_of_notMem hy, zero_add]
      have : ε ≤ ‖y‖ := by simpa [mem_ball_zero_iff] using hy
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_pos (hε.trans_le this), ENNReal.ofReal_rpow_of_pos hε]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hε this hdn)
  have hc : ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff, hε]) measure_ball_lt_top.ne
  have hle : ∫⁻ y in ball (0 : V d) 1, g y ≤ (∫⁻ y, (ball (0 : V d) ε).indicator g y) +
      ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
    calc ∫⁻ y in ball (0 : V d) 1, g y
        ≤ ∫⁻ y in ball (0 : V d) 1, ((ball (0 : V d) ε).indicator g y +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ))) := lintegral_mono fun y => hpt2 y
      _ = (∫⁻ y in ball (0 : V d) 1, (ball (0 : V d) ε).indicator g y) +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _) le_rfl
  have hind : ∫⁻ y, (ball (0 : V d) ε).indicator g y = ⊤ := by
    by_contra hne
    exact (ENNReal.add_ne_top.2 ⟨hne, hc⟩) (eq_top_iff.2 (hT ▸ hle))
  exact eq_top_iff.2 (hind ▸ lintegral_mono_ae hae)

theorem ap_prod_blowup (d k : ℕ) (hd : 1 ≤ d) (hMVd : MVStatement d) (hMVk : MVStatement k)
    (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V d × V k → ℂ,
      DifferentiableOn ℂ u (Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε) →
      ENNReal.ofReal (M * ‖u 0‖ ^ 2) ≤
        ∫⁻ z in Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε,
          ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hvol : volume (ball (0 : V k) ε) ≠ 0 := (measure_ball_pos volume (0 : V k) hε).ne'
  have hsup : ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
    rw [← ENNReal.mul_iSup, apra_blow d hd hMVI ε hε, ENNReal.mul_top hvol]
  have hlt : ENNReal.ofReal M < ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ := by
    rw [hsup]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun τ hτ hτ0 u hu => ?_⟩
  have hIτ : ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ ≤ ∫⁻ x : V d, apraW d ε τ ‖x‖ :=
    lintegral_mono fun x => apraW_anti d ε hτ hτ0 _
  have hslice : ∀ ζ ∈ ball (0 : V k) ε,
      ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
        ∫⁻ x in ball (0 : V d) ε,
          ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) :=
    fun ζ hζ => apra_slice d k hMVd ε τ u hu ζ hζ
  have hbase := apra_base k hMVk ε (fun ζ => u (0, ζ))
    (hu.comp ((differentiableOn_const (0 : V d)).prodMk differentiableOn_id)
      (fun ζ hζ => ⟨mem_ball_self hε, hζ⟩))
  have hmeasF : AEMeasurable
      (fun z : V d × V k => ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))))
      ((volume.restrict (ball (0 : V d) ε)).prod (volume.restrict (ball (0 : V k) ε))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hu' : AEMeasurable u (volume.restrict (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) :=
      hu.continuousOn.aemeasurable (measurableSet_ball.prod measurableSet_ball)
    exact ((hu'.norm.pow_const 2).mul (((measurable_fst.norm.pow_const 2).max
      measurable_const).pow_const _).aemeasurable).ennreal_ofReal
  have hfub : ∫⁻ z in ball (0 : V d) ε ×ˢ ball (0 : V k) ε,
      ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) =
      ∫⁻ ζ in ball (0 : V k) ε, ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeasF]
  rw [hfub]
  calc ENNReal.ofReal (M * ‖u 0‖ ^ 2)
      = ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul' (by positivity), mul_comm]
        rfl
    _ ≤ ENNReal.ofReal (‖u (0, 0)‖ ^ 2) *
          (volume (ball (0 : V k) ε) * ∫⁻ x : V d, apraW d ε τ ‖x‖) :=
        mul_le_mul' le_rfl (hn.le.trans (mul_le_mul' le_rfl hIτ))
    _ = (ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * volume (ball (0 : V k) ε)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := (mul_assoc _ _ _).symm
    _ ≤ (∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := mul_le_mul' hbase le_rfl
    _ ≤ ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := lintegral_mul_const_le _ _
    _ ≤ _ := setLIntegral_mono' measurableSet_ball hslice

end

end ReciprocityTheory.L2DbarEstimates.Y

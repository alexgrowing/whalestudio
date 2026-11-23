import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem multA_integrable_of_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℂ) (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ⊤) :
    Integrable F ν := by
  have h2 : MemLp F 2 ν := by
    refine ⟨hF, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using h
  exact h2.integrable one_le_two

theorem integrableOn_compact_of_locL2 {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasureOnCompacts μ] (u : M → ℂ) (hu : LocalL2Isometry μ u)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  unfold LocalL2Isometry at hu
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact multA_integrable_of_sq (μ.restrict K) u hu.1.restrict (hu.2 K hK)

private lemma localL2Isometry_comp_of_norm_le {M E F : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure M) (f : M → E) (g : E → F)
    (hg : Continuous g) (hb : ∀ e, ‖g e‖ ≤ ‖e‖) (hf : LocalL2Isometry μ f) :
    LocalL2Isometry μ (fun x => g (f x)) := by
  unfold LocalL2Isometry at hf ⊢
  refine ⟨hg.comp_aestronglyMeasurable hf.1, fun C hC => lt_of_le_of_lt ?_ (hf.2 C hC)⟩
  refine lintegral_mono fun x => ?_
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hb _)

theorem locL2_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (f : M → V n) (hf : LocalL2Isometry μ f) (j : Fin n) :
    LocalL2Isometry μ (fun x => f x j) := by
  refine localL2Isometry_comp_of_norm_le μ f (fun v : V n => v j) (EuclideanSpace.proj (𝕜 := ℂ) j).continuous ?_ hf
  intro v
  rw [EuclideanSpace.norm_eq]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)))

theorem locL2_two_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (σ : M → Fin n → Fin n → ℂ) (hσ : LocalL2Isometry μ σ) (j k : Fin n) :
    LocalL2Isometry μ (fun x => σ x j k) := by
  refine localL2Isometry_comp_of_norm_le μ σ (fun s : Fin n → Fin n → ℂ => s j k)
    ((continuous_apply k).comp (continuous_apply j)) ?_ hσ
  intro s
  exact (norm_le_pi_norm (s j) k).trans (norm_le_pi_norm s j)

theorem multA_intOn_w {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (u : M → ℂ) (ph : M → ℝ) (hph : Continuous ph) (hu : AEStronglyMeasurable u μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ < ⊤)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hph.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine multA_integrable_of_sq (μ.restrict K) u hu.restrict ?_
  have hpt : ∀ x ∈ K, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    intro x hx
    have hx' : ph x ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hx)
    have h1 : 1 ≤ Real.exp C * Real.exp (-ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos C).le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖u x‖ ^ 2 = ‖u x‖ ^ 2 * 1 := by ring
      _ ≤ ‖u x‖ ^ 2 * (Real.exp C * Real.exp (-ph x)) := by gcongr
      _ = Real.exp C * (‖u x‖ ^ 2 * Real.exp (-ph x)) := by ring
  calc ∫⁻ x in K, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        setLIntegral_mono_ae' hK.measurableSet (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ := by
        gcongr; exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem multA_int_mul {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) (u c : M → ℂ)
    (hu : ∀ K, IsCompact K → IntegrableOn u K μ) (hc : Continuous c) (hcs : HasCompactSupport c) :
    Integrable (fun x => u x * c x) μ := by
  have h1 : IntegrableOn (fun x => u x * c x) (tsupport c) μ :=
    (hu _ hcs).mul_continuousOn hc.continuousOn hcs
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport c))).mp h1

theorem multA_contR {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [hze]
  have hg := (hph e hc).continuousOn
  have h1 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    (hg.continuousAt (e.open_target.mem_nhds (e.map_source hx))).comp (e.continuousAt hx)
  have h2 : ((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] fun y => (ph y : ℂ) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3

end

end ReciprocityTheory.L2DbarEstimates.F

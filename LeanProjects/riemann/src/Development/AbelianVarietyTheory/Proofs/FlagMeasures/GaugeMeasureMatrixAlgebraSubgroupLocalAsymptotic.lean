import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledIntegralOfDensityOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartAlmostIsometricNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartSurjectiveNearOriginStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem eventually_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} ≤
        ENNReal.ofReal (θ * ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
      ENNReal.ofReal (ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
        ENNReal.ofReal θ * μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} := by
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have h0 : ω ≠ 0 := (measure_ball_pos _ 0 one_pos).ne'
  have ht : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hθ' : 1 < ENNReal.ofReal θ := by simpa using hθ
  have h1 : ω < ENNReal.ofReal θ * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left h0 ht hθ'
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal θ) hμ.2.2 (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hμ.2.2.eventually (gt_mem_nhds h1), h2.eventually (lt_mem_nhds h1),
    self_mem_nhdsWithin] with ρ a1 a2 a3
  have hρ : (0 : ℝ) < ρ := a3
  have hp : ENNReal.ofReal (ρ ^ d) ≠ 0 := by simpa using pow_pos hρ d
  constructor
  · rw [ENNReal.div_lt_iff (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a1
    rw [ENNReal.ofReal_mul (by linarith), mul_right_comm]
    exact a1.le
  · rw [← mul_div_assoc, ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a2
    rw [mul_comm]
    exact a2.le

open scoped Matrix.Norms.Frobenius in
theorem norm_mul_bounds {θ : ℝ} (hθ : 1 < θ) (g Z : Matrix (Fin n) (Fin n) ℂ)
    (hg : ‖g - 1‖ < 1 - θ⁻¹) : ‖g * Z‖ ≤ θ * ‖Z‖ ∧ ‖Z‖ ≤ θ * ‖g * Z‖ := by
  have h1 : ‖g * Z - Z‖ ≤ (1 - θ⁻¹) * ‖Z‖ := by
    have : g * Z - Z = (g - 1) * Z := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [this]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hg.le (norm_nonneg _))
  have h2 := abs_le.1 ((abs_norm_sub_norm_le (g * Z) Z).trans h1)
  have h3 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ (by linarith)
  have h4 : 0 < θ⁻¹ := inv_pos.2 (by linarith)
  have h5 := norm_nonneg Z
  have h6 : 2 - θ⁻¹ ≤ θ := by nlinarith [sq_nonneg (θ - 1)]
  constructor
  · nlinarith
  · have : θ⁻¹ * ‖Z‖ ≤ ‖g * Z‖ := by linarith
    calc ‖Z‖ = θ * (θ⁻¹ * ‖Z‖) := by rw [← mul_assoc, mul_comm θ, h3, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by linarith)

open scoped Matrix.Norms.Frobenius in
theorem density_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) (ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d)) (hψ : Continuous ψ)
    {s : ℝ} (hs : 0 < s)
    (h2 : ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S → ‖uMat g - 1‖ < s → ‖uMat h - 1‖ < s →
      ‖uMat g - uMat h‖ ≤ 2 * ‖ψ g - ψ h‖)
    (hlip : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S →
      ‖uMat g - 1‖ < δ → ‖uMat h - 1‖ < δ →
      ‖ψ g - ψ h‖ ≤ ‖uMat g - uMat h‖ ∧ ‖uMat g - uMat h‖ ≤ κ * ‖ψ g - ψ h‖)
    (hsurj : ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ →
      ∃ g ∈ S, ‖uMat g - 1‖ < δ ∧ ψ g = x)
    (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ → ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) ≤
        ENNReal.ofReal κ * volume (closedBall x r) ∧
      volume (closedBall x r) ≤
        ENNReal.ofReal κ * (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) := by
  obtain ⟨θ, hθκ, hθ⟩ : ∃ θ : ℝ, θ ^ (2 * d + 1) < κ ∧ 1 < θ := by
    have : Tendsto (fun θ : ℝ => θ ^ (2 * d + 1)) (𝓝[>] 1) (𝓝 1) := by
      have : ContinuousAt (fun θ : ℝ => θ ^ (2 * d + 1)) 1 := by fun_prop
      simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    exact ((this.eventually (gt_mem_nhds hκ)).and self_mem_nhdsWithin).exists
  have hθ0 : 0 < θ := by linarith
  obtain ⟨δ₁, hδ₁, hl⟩ := hlip θ hθ
  have hη : 0 < 1 - θ⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hθ)
  obtain ⟨ρ, hρ, hsu⟩ := hsurj (min (min δ₁ s) (1 - θ⁻¹)) (lt_min (lt_min hδ₁ hs) hη)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨g, hgS, hg, rfl⟩ := hsu x hx
  rw [lt_min_iff] at hg
  obtain ⟨hg1, hg3⟩ := hg
  have hgs : ‖uMat g - 1‖ < s := hg1.trans_le (min_le_right _ _)
  have hgδ : ‖uMat g - 1‖ < δ₁ := hg1.trans_le (min_le_left _ _)
  have hae : ∀ᵐ h ∂μ, h ∈ S := hμ.1
  have htr : ∀ t : ℝ, μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ t} =
      μ {k | Real.sqrt (Formalism.REAL.hs (uMat k - 1)) ≤ t} := by
    intro t
    conv_lhs => rw [← hμ.2.1 g hgS]
    rw [(measurableEmbedding_mulLeft g).map_apply]
    congr 1
    ext k
    simp [GlobalTheory.GaugeConst.sqrt_hs]
  have hZ : ∀ h : Formalism.REAL.UJ ε, uMat g * (uMat (g⁻¹ * h) - 1) = uMat h - uMat g := by
    intro h
    rw [Matrix.mul_sub, ← uMat_mul, mul_inv_cancel_left, Matrix.mul_one]
  have htri : ∀ h : Formalism.REAL.UJ ε, ‖uMat h - 1‖ ≤ ‖uMat h - uMat g‖ + ‖uMat g - 1‖ := fun h =>
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  filter_upwards [(GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (pow_pos hθ0 2)).eventually (eventually_bounds hμ hθ),
    (GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (inv_pos.2 hθ0)).eventually (eventually_bounds hμ hθ),
    Ioo_mem_nhdsGT (half_pos (sub_pos.2 hg1))] with r a1 a2 a3
  obtain ⟨hr, hr'⟩ := a3
  have hm1 := min_le_left δ₁ s
  have hm2 := min_le_right δ₁ s
  rw [Measure.map_apply hψ.measurable measurableSet_closedBall,
    Measure.restrict_apply (hψ.measurable measurableSet_closedBall),
    Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  constructor
  · have hsub : μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) ≤
        μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r} := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      obtain ⟨b1, b2⟩ := hh
      have b1' : ‖ψ h - ψ g‖ ≤ r := mem_closedBall_iff_norm.1 b1
      have b3 := h2 h g hS hgS b2 hgs
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).2
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).2
      rw [hZ] at b5
      change ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r
      calc _ ≤ θ * (θ * r) := b5.trans (mul_le_mul_of_nonneg_left
            (b4.trans (mul_le_mul_of_nonneg_left b1' hθ0.le)) hθ0.le)
        _ = _ := by ring
    rw [htr] at hsub
    refine (hsub.trans a1.1).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc θ * (θ ^ 2 * r) ^ d = θ ^ (2 * d + 1) * r ^ d := by ring
      _ ≤ _ := by gcongr
  · have hsub : μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r} ≤
        μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      have hh' : ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r := hh
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).1
      rw [hZ] at b5
      have b6 : ‖uMat h - uMat g‖ ≤ r := by
        refine b5.trans ((mul_le_mul_of_nonneg_left hh' hθ0.le).trans_eq ?_)
        field_simp
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).1
      exact ⟨mem_closedBall_iff_norm.2 (b4.trans b6), show ‖uMat h - 1‖ < s by linarith [htri h]⟩
    rw [htr] at hsub
    have e : ENNReal.ofReal (r ^ d) = ENNReal.ofReal (θ ^ d) * ENNReal.ofReal ((θ⁻¹ * r) ^ d) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel_left₀ hθ0.ne']
    rw [e, mul_assoc]
    refine (mul_le_mul_right a2.2 _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    calc θ ^ d * θ = θ ^ (d + 1) := by ring
      _ ≤ θ ^ (2 * d + 1) := pow_le_pow_right₀ hθ.le (by omega)
      _ ≤ _ := hθκ.le

open scoped Matrix.Norms.Frobenius in

theorem gauge_local_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub {g | uMat g - 1 ∈ A} d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ (∀ μ', IsGaugeSub {g | uMat g - 1 ∈ A} d μ' → μ' = μ) ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ r₀ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | Formalism.REAL.hs (uMat g - 1) < r₁}, φ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re / r) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t)) := by
  intro n ε A d E hA hE hV μ hμ
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.isRiemannianHaarOnSubgroup_sigmaFinite_unique n ε (algSub ε A hA) (isClosed_algSub A hA) d μ hμ
  refine ⟨a1, a2, a3, ?_⟩
  have hlip := GlobalTheory.T.unitarySubgroupChart_almost_isometric_near_one n ε A d E hA hE hV
  have hsurj := GlobalTheory.T.unitarySubgroupChart_surjective_near_origin n ε A d E hA hE hV
  simp only [GlobalTheory.GaugeConst.sqrt_hs] at hlip hsurj
  set ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d) :=
    fun g => WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) with hψdef
  have hψ : Continuous ψ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => Complex.continuous_re.comp ?_)
    exact (((GlobalTheory.GaugeConst.continuous_uMat ε).sub continuous_const).matrix_mul
      continuous_const).matrix_trace
  obtain ⟨δ, hδ, h2⟩ := hlip 2 one_lt_two
  obtain ⟨s₀, ⟨hs1, -⟩, hs2, hs3⟩ :=
    ((eventually_bounds hμ one_lt_two).and (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨s₀ ^ 2, by positivity, fun r₁ hr₁ hr₁' φ hφ hφc => ?_⟩
  have hs : 0 < Real.sqrt r₁ := Real.sqrt_pos.2 hr₁
  have hs' : Real.sqrt r₁ ≤ s₀ := Real.sqrt_le_iff.2 ⟨hs2.le, hr₁'⟩
  have hset : {g : Formalism.REAL.UJ ε | Formalism.REAL.hs (uMat g - 1) < r₁} =
      {g | ‖uMat g - 1‖ < Real.sqrt r₁} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← GlobalTheory.GaugeConst.sqrt_hs]
    exact (Real.sqrt_lt_sqrt_iff_of_pos hr₁).symm
  rw [hset]
  have hfin : IsFiniteMeasure (μ.restrict {g | ‖uMat g - 1‖ < Real.sqrt r₁}) := by
    refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (le_trans (measure_mono ?_) hs1))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · intro g hg
      simp only [Set.mem_ofPred_eq, GlobalTheory.GaugeConst.sqrt_hs] at hg ⊢
      linarith
  have hd := density_bounds hμ ψ hψ hs
    (fun g h hg hh b1 b2 => (h2 g h hg hh (by linarith) (by linarith)).2) hlip hsurj
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hΦ : Continuous (fun x : EuclideanSpace ℝ (Fin d) => φ (e x)) := hφ.comp e.continuous
  have hv := GlobalTheory.T.tendsto_rescaled_integral_of_ball_density_bounds d _ inferInstance hd (fun x => φ (e x)) hΦ
    (hφc.comp_homeomorph e.toHomeomorph)
  have hI : ∫ x : EuclideanSpace ℝ (Fin d), φ (e x) = ∫ t, φ t :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp' φ
  rw [hI] at hv
  refine hv.congr fun r => ?_
  rw [integral_map (f := fun x => φ (e (r⁻¹ • x))) hψ.aemeasurable (hΦ.comp (continuous_const_smul r⁻¹)).aestronglyMeasurable]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  refine congrArg φ (funext fun i => ?_)
  simp [e, hψdef, div_eq_inv_mul]

end GlobalTheory.GaugeSubLoc

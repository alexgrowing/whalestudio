import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem closIneq_sq_le (a b η : ℝ) (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2 := by
  have hi : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  have key : η * ((1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2) - η * (a + b) ^ 2 = (η * a - b) ^ 2 := by
    linear_combination b ^ 2 * hi
  have h2 : η * (a + b) ^ 2 ≤ η * ((1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2) := by
    nlinarith [key, sq_nonneg (η * a - b)]
  exact le_of_mul_le_mul_left h2 hη

theorem closIneq_norm_sq_le {E : Type*} [SeminormedAddCommGroup E] (x y : E) (η : ℝ) (hη : 0 < η) :
    ‖x + y‖ ^ 2 ≤ (1 + η) * ‖x‖ ^ 2 + (1 + η⁻¹) * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y]
  exact h2.trans (closIneq_sq_le _ _ η hη)

theorem closIneq_key {X P Q : ℝ≥0∞} (hQ : Q ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → X ≤ P + ENNReal.ofReal δ * Q) : X ≤ P := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨q, rfl⟩ : ∃ q : NNReal, Q = q := ⟨Q.toNNReal, (ENNReal.coe_toNNReal hQ).symm⟩
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  set δ : ℝ := min 1 ((ε : ℝ) / ((q : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε' hq1)
  refine (h δ hδpos (min_le_left _ _)).trans (add_le_add le_rfl ?_)
  have hle : δ * q ≤ ε := by
    have h1 : δ ≤ (ε : ℝ) / ((q : ℝ) + 1) := min_le_right _ _
    have h3 : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hq1]
      linarith
    calc δ * q ≤ (ε : ℝ) / ((q : ℝ) + 1) * q := mul_le_mul_of_nonneg_right h1 q.2
      _ = (ε : ℝ) * ((q : ℝ) / ((q : ℝ) + 1)) := by ring
      _ ≤ (ε : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = ε := mul_one _
  calc ENNReal.ofReal δ * (q : ENNReal) = ENNReal.ofReal (δ * q) := by
        rw [ENNReal.ofReal_mul hδpos.le, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hle
    _ = ε := ENNReal.ofReal_coe_nnreal

theorem closIneq_lint_ip_le {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M) (φ : M → ℝ)
    (hφ : Measurable φ) (v h : M → V n) (hv : AEStronglyMeasurable v μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ^ 2 ≤
      (∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) ∂μ) *
        ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) ∂μ := by
  set F : M → ENNReal := fun x => ENNReal.ofReal (‖v x‖ * Real.exp (-φ x / 2)) with hFd
  set G : M → ENNReal := fun x => ENNReal.ofReal (‖h x‖ * Real.exp (-φ x / 2)) with hGd
  have hpt : ∀ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ≤ F x * G x := by
    intro x
    rw [hFd, hGd]
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-φ x) = Real.exp (-φ x / 2) * Real.exp (-φ x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖⟪v x, h x⟫_ℂ‖ * Real.exp (-φ x) ≤ ‖v x‖ * ‖h x‖ * Real.exp (-φ x) :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (Real.exp_pos _).le
      _ = ‖v x‖ * Real.exp (-φ x / 2) * (‖h x‖ * Real.exp (-φ x / 2)) := by
          rw [he]
          ring
  have hsq2 : ∀ (a : ℝ) (x : M), (a * Real.exp (-φ x / 2)) ^ 2 = a ^ 2 * Real.exp (-φ x) := by
    intro a x
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hF2 : ∀ x, F x ^ (2 : ℝ) = ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) := by
    intro x
    rw [hFd]
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, hsq2]
  have hG2 : ∀ x, G x ^ (2 : ℝ) = ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) := by
    intro x
    rw [hGd]
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, hsq2]
  have hsq : ∀ A : ENNReal, (A ^ (1 / (2 : ℝ))) ^ 2 = A := by
    intro A
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hE : Measurable fun x => Real.exp (-φ x / 2) := (hφ.neg.div_const 2).exp
  have hFm : AEMeasurable F μ := (hv.norm.aemeasurable.mul hE.aemeasurable).ennreal_ofReal
  have hGm : AEMeasurable G μ := (hh.norm.aemeasurable.mul hE.aemeasurable).ennreal_ofReal
  have hint : (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ≤ ∫⁻ x, (F * G) x ∂μ :=
    lintegral_mono fun x => hpt x
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) (by constructor <;> norm_num) hFm hGm
  calc (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (zero_le) (hint.trans hH) 2
    _ = (∫⁻ x, F x ^ (2 : ℝ) ∂μ) * ∫⁻ x, G x ^ (2 : ℝ) ∂μ := by
        rw [mul_pow, hsq, hsq]
    _ = _ := by
        simp only [hF2, hG2]

theorem closIneq_integrable {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M) (φ : M → ℝ)
    (hφ : Measurable φ) (v h : M → V n) (hv : AEStronglyMeasurable v μ)
    (hh : AEStronglyMeasurable h μ)
    (hv2 : ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) ∂μ < ⊤)
    (hh2 : ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) ∂μ < ⊤) :
    Integrable (fun x => ⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)) μ := by
  refine ⟨(hv.inner hh).mul (Complex.measurable_ofReal.comp hφ.neg.exp).aestronglyMeasurable, ?_⟩
  have h1 := closIneq_lint_ip_le μ φ hφ v h hv hh
  have hlt := lt_of_le_of_lt h1 (ENNReal.mul_lt_top hv2 hh2)
  show ∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ < ⊤
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc] at hlt
  simp at hlt

theorem closIneq_continuous_form {M : Type*} [TopologicalSpace M] {n : ℕ} (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → V n) (hg : IsTestForm n z g) : Continuous g := by
  have hcoord : ∀ j, Continuous fun x => g x j := by
    intro j
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, hze⟩ := hz x
    have hch : IsChart n z e := fun y _ => congrFun hze y
    have hC := ((hg j).1 e hch).continuousOn
    have h1 : ContinuousAt ((fun x => g x j) ∘ e.symm) (e x) :=
      hC.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
    have h2 : ContinuousAt (((fun x => g x j) ∘ e.symm) ∘ e) x :=
      h1.comp (e.continuousAt hxe)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    simp [e.left_inv hy]
  have h3 : Continuous fun x => EuclideanSpace.equiv (Fin n) ℂ (g x) :=
    continuous_pi fun j => hcoord j
  have h4 := (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp h3
  convert h4 using 1
  funext x
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm_apply_apply (g x)).symm

private lemma continuous_of_smoothR' {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {f : M → ℝ} (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous fun x => (f x : ℂ) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, hze⟩ := hz x
    have hch : IsChart n z e := fun y _ => congrFun hze y
    have hC := (hf e hch).continuousOn
    have h1 : ContinuousAt ((fun x => (f x : ℂ)) ∘ e.symm) (e x) :=
      hC.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
    refine (h1.comp (e.continuousAt hxe)).congr ?_
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    simp [e.left_inv hy]
  have h := Complex.continuous_re.comp hc
  convert h using 1
  funext x
  simp

private lemma ofReal_norm_ipV_sq_le_mul_nV {M : Type*} [MeasurableSpace M] {n : ℕ} (z : M → V n) (φ : M → ℝ)
    (hφ : Measurable φ) (v h : M → V n) (hv : AEStronglyMeasurable v (vol n z))
    (hh : AEStronglyMeasurable h (vol n z)) :
    ENNReal.ofReal (‖ipV n z v h φ‖ ^ 2) ≤ nV n z v φ * nV n z h φ := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  unfold ipV nV
  exact (pow_le_pow_left₀ zero_le (enorm_integral_le_lintegral_enorm _) 2).trans
    (closIneq_lint_ip_le (vol n z) φ hφ v h hv hh)

private lemma lintegral_weighted_norm_add_sq_le {M : Type*} [MeasurableSpace M] {E : Type*} [NormedAddCommGroup E]
    (μ : Measure M) (φ : M → ℝ) (hφ : Measurable φ) (u u' : M → E)
    (hu : AEStronglyMeasurable u μ) (η : ℝ) (hη : 0 < η) :
    ∫⁻ x, ENNReal.ofReal (‖u x + u' x‖ ^ 2 * Real.exp (-φ x)) ∂μ ≤
      ENNReal.ofReal (1 + η) * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-φ x)) ∂μ +
      ENNReal.ofReal (1 + η⁻¹) * ∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2 * Real.exp (-φ x)) ∂μ := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (1 + η) *
      ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-φ x))) μ :=
    aemeasurable_const.mul
      ((hu.norm.aemeasurable.pow_const 2).mul hφ.neg.exp.aemeasurable).ennreal_ofReal
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hm]
  refine lintegral_mono fun x => ?_
  have he := Real.exp_pos (-φ x)
  have h1η : (0 : ℝ) ≤ 1 + η := by linarith
  have h2η : (0 : ℝ) ≤ 1 + η⁻¹ := by positivity
  rw [← ENNReal.ofReal_mul h1η, ← ENNReal.ofReal_mul h2η,
    ← ENNReal.ofReal_add (mul_nonneg h1η (mul_nonneg (sq_nonneg ‖u x‖) he.le))
      (mul_nonneg h2η (mul_nonneg (sq_nonneg ‖u' x‖) he.le))]
  apply ENNReal.ofReal_le_ofReal
  calc ‖u x + u' x‖ ^ 2 * Real.exp (-φ x)
      ≤ ((1 + η) * ‖u x‖ ^ 2 + (1 + η⁻¹) * ‖u' x‖ ^ 2) * Real.exp (-φ x) :=
        mul_le_mul_of_nonneg_right (closIneq_norm_sq_le _ _ η hη) he.le
    _ = _ := by ring

theorem closureIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hDens : DensStatement n M) : ClosureIneqStatement n M := by
  intro z hz e ph ψ v B ε he hph hψ hcut hv hB hε hineq f w hf hw hadj hS
  have hphm := (continuous_of_smoothR' hz hph).measurable
  have hψm := (continuous_of_smoothR' hz hψ).measurable
  have hw2m : Measurable (w2 ph ψ) := hphm.sub hψm
  have hw1m : Measurable (w1 ph ψ) := hphm.sub (hψm.const_mul 2)
  have h0 : MemWeightedL2TwoForm n z 0 ph := ⟨aestronglyMeasurable_const, by unfold n2; simp [sq2]⟩
  have hGA := hDens z hz e ph ψ he hph hψ hcut f w 0 hf hw h0 hadj hS
  have hWt : wint n z w (w1 ph ψ) ≠ ⊤ := hw.2.ne
  have hNt : nV n z v (w2 ph ψ) ≠ ⊤ := hv.2.ne
  have hct : ENNReal.ofReal (1 + ε) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPt : B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ)) ≠ ⊤ :=
    ENNReal.mul_ne_top hB (ENNReal.mul_ne_top hct hWt)
  have hQt : 3 * (B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ))) +
      2 * (2 * B * ENNReal.ofReal (1 + ε) + B) + 2 * nV n z v (w2 ph ψ) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hPt,
      ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hB) hct, hB⟩)⟩,
      ENNReal.mul_ne_top (by simp) hNt⟩
  refine closIneq_key hQt fun δ hδ hδ1 => ?_
  obtain ⟨g, hgT, h1, h2, h3⟩ := hGA (ENNReal.ofReal (δ ^ 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hgm : AEStronglyMeasurable g (vol n z) :=
    (closIneq_continuous_form z hz g hgT).aestronglyMeasurable
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hofr1 : ENNReal.ofReal (1 + δ) = 1 + ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_add zero_le_one hδ.le, ENNReal.ofReal_one]
  have hsmall : ENNReal.ofReal (1 + δ⁻¹) * ENNReal.ofReal (δ ^ 2) ≤ 2 * ENNReal.ofReal δ := by
    have hinv : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
    have he1 : (1 + δ⁻¹) * δ ^ 2 = δ ^ 2 + δ := by linear_combination δ * hinv
    rw [← ENNReal.ofReal_mul (by positivity), he1]
    calc ENNReal.ofReal (δ ^ 2 + δ) ≤ ENNReal.ofReal (2 * δ) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 * ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have ha1 : ENNReal.ofReal δ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hδ1
  have hfg : nV n z (fun x => f x - g x) (w2 ph ψ) ≤ ENNReal.ofReal (δ ^ 2) := by
    have hsw : nV n z (fun x => f x - g x) (w2 ph ψ) = nV n z (fun x => g x - f x) (w2 ph ψ) := by
      unfold nV
      congr 1
      funext x
      rw [norm_sub_rev]
    rw [hsw]
    exact h1.le
  have hgfin : nV n z g (w2 ph ψ) < ⊤ := by
    have hC := lintegral_weighted_norm_add_sq_le (vol n z) (w2 ph ψ) hw2m f (fun x => g x - f x) hf.1 1 one_pos
    have hfg' : ∀ x, f x + (g x - f x) = g x := fun x => by abel
    simp only [hfg'] at hC
    exact lt_of_le_of_lt hC (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h1.trans ENNReal.ofReal_lt_top)⟩)
  have hig := closIneq_integrable (vol n z) (w2 ph ψ) hw2m v g hv.1 hgm hv.2 hgfin
  have hifg := closIneq_integrable (vol n z) (w2 ph ψ) hw2m v (fun x => f x - g x) hv.1
    (hf.1.sub hgm) hv.2 (hfg.trans_lt ENNReal.ofReal_lt_top)
  have hsplit : ipV n z v f (w2 ph ψ) =
      ipV n z v g (w2 ph ψ) + ipV n z v (fun x => f x - g x) (w2 ph ψ) := by
    unfold ipV
    rw [← integral_add hig hifg]
    congr 1
    funext x
    simp only [inner_sub_right]
    ring
  have hwT : wint n z (tstar n z (w1 ph ψ) (w2 ph ψ) g) (w1 ph ψ) ≤
      (1 + ENNReal.ofReal δ) * wint n z w (w1 ph ψ) + 2 * ENNReal.ofReal δ := by
    have hC := lintegral_weighted_norm_add_sq_le (vol n z) (w1 ph ψ) hw1m w
      (fun x => tstar n z (w1 ph ψ) (w2 ph ψ) g x - w x) hw.1 δ hδ
    have hTw : ∀ x, w x + (tstar n z (w1 ph ψ) (w2 ph ψ) g x - w x) =
        tstar n z (w1 ph ψ) (w2 ph ψ) g x := fun x => by ring
    simp only [hTw] at hC
    rw [hofr1] at hC
    refine hC.trans (add_le_add le_rfl ?_)
    calc _ ≤ ENNReal.ofReal (1 + δ⁻¹) * ENNReal.ofReal (δ ^ 2) := by
          gcongr
          exact h2.le
      _ ≤ _ := hsmall
  have hS2 : n2 n z (sbar n z g) ph ≤ ENNReal.ofReal δ := by
    simp only [Pi.zero_apply, sub_zero] at h3
    exact h3.le.trans (ENNReal.ofReal_le_ofReal hδsq)
  have h1δ : (0 : ℝ) ≤ 1 + δ := by linarith
  have h2δ : (0 : ℝ) ≤ 1 + δ⁻¹ := by positivity
  have hIg := (hineq g hgT).trans (by gcongr : B * (ENNReal.ofReal (1 + ε) *
      wint n z (tstar n z (w1 ph ψ) (w2 ph ψ) g) (w1 ph ψ) + n2 n z (sbar n z g) ph) ≤
      B * (ENNReal.ofReal (1 + ε) * ((1 + ENNReal.ofReal δ) * wint n z w (w1 ph ψ) +
        2 * ENNReal.ofReal δ) + ENNReal.ofReal δ))
  have hIfg := (ofReal_norm_ipV_sq_le_mul_nV z (w2 ph ψ) hw2m v (fun x => f x - g x) hv.1 (hf.1.sub hgm)).trans
    (by gcongr : nV n z v (w2 ph ψ) * nV n z (fun x => f x - g x) (w2 ph ψ) ≤
      nV n z v (w2 ph ψ) * ENNReal.ofReal (δ ^ 2))
  calc ENNReal.ofReal (‖ipV n z v f (w2 ph ψ)‖ ^ 2)
      = ENNReal.ofReal (‖ipV n z v g (w2 ph ψ) + ipV n z v (fun x => f x - g x) (w2 ph ψ)‖ ^ 2) := by
        rw [hsplit]
    _ ≤ ENNReal.ofReal ((1 + δ) * ‖ipV n z v g (w2 ph ψ)‖ ^ 2 +
          (1 + δ⁻¹) * ‖ipV n z v (fun x => f x - g x) (w2 ph ψ)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (closIneq_norm_sq_le _ _ δ hδ)
    _ = ENNReal.ofReal (1 + δ) * ENNReal.ofReal (‖ipV n z v g (w2 ph ψ)‖ ^ 2) +
          ENNReal.ofReal (1 + δ⁻¹) *
            ENNReal.ofReal (‖ipV n z v (fun x => f x - g x) (w2 ph ψ)‖ ^ 2) := by
        rw [ENNReal.ofReal_add (mul_nonneg h1δ (sq_nonneg _)) (mul_nonneg h2δ (sq_nonneg _)),
          ENNReal.ofReal_mul h1δ, ENNReal.ofReal_mul h2δ]
    _ ≤ (1 + ENNReal.ofReal δ) * (B * (ENNReal.ofReal (1 + ε) * ((1 + ENNReal.ofReal δ) *
          wint n z w (w1 ph ψ) + 2 * ENNReal.ofReal δ) + ENNReal.ofReal δ)) +
          ENNReal.ofReal (1 + δ⁻¹) * (nV n z v (w2 ph ψ) * ENNReal.ofReal (δ ^ 2)) := by
        rw [hofr1]
        gcongr
    _ = (1 + ENNReal.ofReal δ) * (B * (ENNReal.ofReal (1 + ε) * ((1 + ENNReal.ofReal δ) *
          wint n z w (w1 ph ψ) + 2 * ENNReal.ofReal δ) + ENNReal.ofReal δ)) +
          nV n z v (w2 ph ψ) * (ENNReal.ofReal (1 + δ⁻¹) * ENNReal.ofReal (δ ^ 2)) := by ring
    _ ≤ (1 + ENNReal.ofReal δ) * (B * (ENNReal.ofReal (1 + ε) * ((1 + ENNReal.ofReal δ) *
          wint n z w (w1 ph ψ) + 2 * ENNReal.ofReal δ) + ENNReal.ofReal δ)) +
          nV n z v (w2 ph ψ) * (2 * ENNReal.ofReal δ) :=
        by gcongr
    _ = B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ)) + ENNReal.ofReal δ *
          ((2 + ENNReal.ofReal δ) * (B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ))) +
            (1 + ENNReal.ofReal δ) * (2 * B * ENNReal.ofReal (1 + ε) + B) +
            2 * nV n z v (w2 ph ψ)) := by ring
    _ ≤ B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ)) + ENNReal.ofReal δ *
          (3 * (B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ))) +
            2 * (2 * B * ENNReal.ofReal (1 + ε) + B) + 2 * nV n z v (w2 ph ψ)) := by
        have h2a : 2 + ENNReal.ofReal δ ≤ 3 := by
          calc 2 + ENNReal.ofReal δ ≤ 2 + 1 := add_le_add le_rfl ha1
            _ = 3 := by norm_num
        have h1a : 1 + ENNReal.ofReal δ ≤ 2 := by
          calc 1 + ENNReal.ofReal δ ≤ 1 + 1 := add_le_add le_rfl ha1
            _ = 2 := by norm_num
        gcongr

end

end ReciprocityTheory.L2DbarEstimates.F

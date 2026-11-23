import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem cut_sq_add_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    first
    | exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    | (gcongr; exact norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cut_sq_sub_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    first
    | exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
    | (gcongr; exact norm_sub_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem two_form_sq_nonneg (n : ℕ) (σ : Fin n → Fin n → ℂ) : 0 ≤ sq2 n σ := by
  simp only [sq2]
  first
  | positivity
  | exact div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)

theorem two_form_sq_add_le (n : ℕ) (a b : Fin n → Fin n → ℂ) :
    sq2 n (fun j k => a j k + b j k) ≤ 2 * sq2 n a + 2 * sq2 n b := by
  simp only [sq2]
  have h : ∑ j, ∑ k, ‖a j k + b j k‖ ^ 2 ≤
      ∑ j, ∑ k, (2 * ‖a j k‖ ^ 2 + 2 * ‖b j k‖ ^ 2) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => cut_sq_add_le _ _
  have e : ∑ j, ∑ k, (2 * ‖a j k‖ ^ 2 + 2 * ‖b j k‖ ^ 2) =
      2 * ∑ j, ∑ k, ‖a j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖b j k‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith

theorem two_form_sq_smul (n : ℕ) (c : ℂ) (a : Fin n → Fin n → ℂ) :
    sq2 n (fun j k => c * a j k) = ‖c‖ ^ 2 * sq2 n a := by
  simp only [sq2, norm_mul, mul_pow, ← Finset.mul_sum]
  ring

theorem two_form_sq_wedge_le (n : ℕ) (a b : Fin n → ℂ) :
    sq2 n (wedge a b) ≤ 2 * (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  unfold sq2 wedge
  have h : ∀ j k, ‖a j * b k - a k * b j‖ ^ 2 ≤
      2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2) := by
    intro j k
    have := cut_sq_sub_le (a j * b k) (a k * b j)
    simpa [mul_pow] using this
  have h2 : ∑ j, ∑ k, ‖a j * b k - a k * b j‖ ^ 2 ≤
      ∑ j, ∑ k, (2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h j k
  have e1 : ∑ j, ∑ k, ‖a j‖ ^ 2 * ‖b k‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    rw [Finset.sum_mul_sum]
  have e2 : ∑ j, ∑ k, ‖a k‖ ^ 2 * ‖b j‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
  have e3 : ∑ j, ∑ k, (2 * (‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (‖a k‖ ^ 2 * ‖b j‖ ^ 2)) =
      2 * (∑ j, ∑ k, ‖a j‖ ^ 2 * ‖b k‖ ^ 2) + 2 * (∑ j, ∑ k, ‖a k‖ ^ 2 * ‖b j‖ ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e3, e1, e2] at h2
  linarith

theorem cut_cs (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by
  have h1 : ‖∑ j, a j * b j‖ ≤ ∑ j, ‖a j‖ * ‖b j‖ := by
    calc ‖∑ j, a j * b j‖ ≤ ∑ j, ‖a j * b j‖ := norm_sum_le _ _
      _ = ∑ j, ‖a j‖ * ‖b j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖b j‖)
  calc ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by
        first
        | exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        | gcongr
    _ ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := h2

theorem cut_d_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    d n z j f x = d n z j g x := by
  unfold d
  split_ifs with hc
  · have hs := Classical.choose_spec hc
    generalize Classical.choose hc = e at hs ⊢
    obtain ⟨hch, hxs⟩ := hs
    have hzx : z x = e x := hch hxs
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm hxs
      | (have h0 := e.continuousAt_symm (e.map_source hxs)
         unfold ContinuousAt at h0
         rwa [e.left_inv hxs] at h0)
    have hev : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact h.comp_tendsto ht
    unfold wd
    rw [hev.fderiv_eq]
  · rfl

theorem cut_db_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  unfold db
  split_ifs with hc
  · have hs := Classical.choose_spec hc
    generalize Classical.choose hc = e at hs ⊢
    obtain ⟨hch, hxs⟩ := hs
    have hzx : z x = e x := hch hxs
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm hxs
      | (have h0 := e.continuousAt_symm (e.map_source hxs)
         unfold ContinuousAt at h0
         rwa [e.left_inv hxs] at h0)
    have hev : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact h.comp_tendsto ht
    unfold wdb
    rw [hev.fderiv_eq]
  · rfl

theorem cut_d_eq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (η : M → ℝ) (U : Set M) (hU : IsOpen U)
    (hη : ∀ y ∈ U, η y = 1) (x : M) (hx : x ∈ U) :
    d n z j (fun y => (η y : ℂ)) x = 0 ∧ db n z j (fun y => (η y : ℂ)) x = 0 := by
  have hev : (fun y => (η y : ℂ)) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hη y hy]
  rw [cut_d_congr n z hz j _ _ x hev, cut_db_congr n z hz j _ _ x hev]
  constructor
  · unfold d
    split_ifs
    · simp [wd, Function.comp_def]
    · rfl
  · unfold db
    split_ifs
    · simp [wdb, Function.comp_def]
    · rfl

private lemma norm_wd_ofReal_eq_norm_wdb_ofReal (n : ℕ) (j : Fin n) (h : V n → ℝ) (y : V n) :
    ‖wd n j (fun y => (h y : ℂ)) y‖ = ‖wdb n j (fun y => (h y : ℂ)) y‖ := by
  have key : ∀ v : V n, (starRingEnd ℂ) (fderiv ℝ (fun y => (h y : ℂ)) y v) =
      fderiv ℝ (fun y => (h y : ℂ)) y v := by
    intro v
    have hf : (fun y => (h y : ℂ)) = Complex.conjCLE ∘ (fun y => (h y : ℂ)) := by
      funext w
      simp
    conv_rhs => rw [hf]
    rw [ContinuousLinearEquiv.comp_fderiv]
    simp
  unfold wd wdb
  rw [← Complex.norm_conj]
  congr 1
  simp only [map_div₀, map_sub, map_add, map_mul, key, Complex.conj_I, map_ofNat]
  ring

theorem cut_norm_d_eq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (η : M → ℝ) (x : M) :
    ‖d n z j (fun y => (η y : ℂ)) x‖ = ‖db n z j (fun y => (η y : ℂ)) x‖ := by
  unfold d db
  split_ifs with hc
  · exact norm_wd_ofReal_eq_norm_wdb_ofReal n j (η ∘ (Classical.choose hc).symm) (z x)
  · rfl

theorem SmoothR.cut_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  unfold SmoothR Smooth at hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, hze⟩ := hz x
  have hch : IsChart n z e := by
    unfold IsChart
    rw [hze]
    exact Set.eqOn_refl _ _
  have hco : ContinuousOn ((fun x => (f x : ℂ)) ∘ e.symm) e.target := (hf e hch).continuousOn
  have h1 : ContinuousAt ((fun x => (f x : ℂ)) ∘ e.symm) (e x) :=
    hco.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
  have h2 : ContinuousAt (((fun x => (f x : ℂ)) ∘ e.symm) ∘ e) x :=
    ContinuousAt.comp (f := e) h1 (e.continuousAt hxe)
  have hev : ((fun x => (f x : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] (fun x => (f x : ℂ)) := by
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    simp [e.left_inv hy]
  have h3 : ContinuousAt (fun x => (f x : ℂ)) x := by
    first
    | exact h2.congr hev
    | exact h2.congr_of_eventuallyEq hev.symm
  have h4 : ContinuousAt (fun y => ((f y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4

theorem locL2_of_weighted_bound {M E : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] [NormedAddCommGroup E]
    (μ : Measure M) (u : M → E) (q ph : M → ℝ) (c : ℝ) (hc : 0 ≤ c) (hph : Continuous ph)
    (hu : AEStronglyMeasurable u μ) (hq : ∀ x, ‖u x‖ ^ 2 ≤ c * q x)
    (h : ∫⁻ x, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ < ⊤) : LocalL2Isometry μ u := by
  unfold LocalL2Isometry
  refine ⟨hu, fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hC.bddAbove_image hph.continuousOn
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hpt : ∀ x ∈ C, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (c * Real.exp K) * ENNReal.ofReal (q x * Real.exp (-ph x)) := by
    intro x hx
    have hphK : ph x ≤ K := hK ⟨x, hx, rfl⟩
    have hE : Real.exp (ph x) ≤ Real.exp K := Real.exp_le_exp.2 hphK
    have hF : 0 < Real.exp (-ph x) := Real.exp_pos _
    have hEF : Real.exp (ph x) * Real.exp (-ph x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcq : 0 ≤ c * q x := le_trans (sq_nonneg _) (hq x)
    have hEF' : c * q x * (Real.exp (ph x) * Real.exp (-ph x)) = c * q x := by
      rw [hEF, mul_one]
    have hprod := mul_nonneg (mul_nonneg hcq hF.le) (sub_nonneg.2 hE)
    have hq' := hq x
    have hb : ‖u x‖ ^ 2 ≤ (c * Real.exp K) * (q x * Real.exp (-ph x)) := by
      nlinarith [hEF', hprod, hq']
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ x in C, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in C, ENNReal.ofReal (c * Real.exp K) * ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ := by
        first
        | exact setLIntegral_mono' hCm hpt
        | exact lintegral_mono_ae ((ae_restrict_iff' hCm).2 (ae_of_all _ hpt))
    _ = ENNReal.ofReal (c * Real.exp K) * ∫⁻ x in C, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c * Real.exp K) * ∫⁻ x, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ := by
        gcongr
        first
        | exact Measure.restrict_le_self
        | exact setLIntegral_le_lintegral _ _
        | exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem cut_lint_tri {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G H : M → ℝ≥0∞)
    (hG : AEMeasurable G μ) (h : ∀ x, F x ≤ 2 * H x + 2 * G x) :
    ∫⁻ x, F x ∂μ ≤ 2 * ∫⁻ x, H x ∂μ + 2 * ∫⁻ x, G x ∂μ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, (2 * H x + 2 * G x) ∂μ := lintegral_mono h
    _ = ∫⁻ x, 2 * H x ∂μ + ∫⁻ x, 2 * G x ∂μ := lintegral_add_right' _ (hG.const_mul 2)
    _ = 2 * ∫⁻ x, H x ∂μ + 2 * ∫⁻ x, G x ∂μ := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]

def cutW {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ η : M → ℝ)
    (f : M → V n) (w : M → ℂ) : M → ℂ := fun x =>
  (η x : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
    ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j

def cutS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ)
    (f : M → V n) (σ : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ := fun x j k =>
  (η x : ℂ) * σ x j k + wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k

private lemma norm_ofReal_sq_le_one_of_abs_le_one (c : ℝ) (hc : |c| ≤ 1) : ‖(c : ℂ)‖ ^ 2 ≤ 1 := by
  have h1 : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hc
  nlinarith [norm_nonneg (c : ℂ)]

theorem cut_ptF {n : ℕ} (c : ℝ) (hc : |c| ≤ 1) (v : V n) : ‖(c : ℂ) • v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow]
  have h2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg ‖v‖)]

theorem cut_ptW (c : ℝ) (hc : |c| ≤ 1) (wx S : ℂ) (fx2 D ph ψ : ℝ) (hS : ‖S‖ ^ 2 ≤ D * fx2)
    (hD : D ≤ Real.exp ψ) (hf2 : 0 ≤ fx2) :
    ‖(c : ℂ) * wx - (Real.exp (-ψ) : ℂ) * S‖ ^ 2 * Real.exp (-(ph - 2 * ψ)) ≤
      2 * (‖wx‖ ^ 2 * Real.exp (-(ph - 2 * ψ))) + 2 * (fx2 * Real.exp (-(ph - ψ))) := by
  have h1 := cut_sq_sub_le ((c : ℂ) * wx) ((Real.exp (-ψ) : ℂ) * S)
  have hc2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  have h2 : ‖(c : ℂ) * wx‖ ^ 2 ≤ ‖wx‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg ‖wx‖)]
  have h3 : ‖(Real.exp (-ψ) : ℂ) * S‖ ^ 2 = Real.exp (-ψ) ^ 2 * ‖S‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hP : 0 < Real.exp (-(ph - 2 * ψ)) := Real.exp_pos _
  have hPQ : Real.exp (-(ph - 2 * ψ)) = Real.exp (-(ph - ψ)) * Real.exp ψ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hAB : Real.exp (-ψ) * Real.exp ψ = 1 := by
    rw [← Real.exp_add]
    simp
  have hS' : Real.exp (-ψ) ^ 2 * ‖S‖ ^ 2 ≤ Real.exp (-ψ) ^ 2 * (D * fx2) :=
    mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have hD' : Real.exp (-ψ) ^ 2 * (D * fx2) ≤ Real.exp (-ψ) ^ 2 * (Real.exp ψ * fx2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hf2) (sq_nonneg _)
  calc ‖(c : ℂ) * wx - (Real.exp (-ψ) : ℂ) * S‖ ^ 2 * Real.exp (-(ph - 2 * ψ))
      ≤ (2 * ‖wx‖ ^ 2 + 2 * (Real.exp (-ψ) ^ 2 * (Real.exp ψ * fx2))) * Real.exp (-(ph - 2 * ψ)) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        linarith
    _ = 2 * (‖wx‖ ^ 2 * Real.exp (-(ph - 2 * ψ))) + 2 * (fx2 * Real.exp (-(ph - ψ))) := by
        rw [hPQ]
        linear_combination (2 * fx2 * Real.exp (-(ph - ψ)) * (Real.exp (-ψ) * Real.exp ψ + 1)) * hAB

theorem cut_ptS {n : ℕ} (c : ℝ) (hc : |c| ≤ 1) (σx : Fin n → Fin n → ℂ) (a b : Fin n → ℂ)
    (D fx2 ph ψ : ℝ) (ha : ∑ i, ‖a i‖ ^ 2 = D) (hb : ∑ i, ‖b i‖ ^ 2 = fx2)
    (hD : D ≤ Real.exp ψ) :
    sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) * Real.exp (-ph) ≤
      2 * (sq2 n σx * Real.exp (-ph)) + 4 * (fx2 * Real.exp (-(ph - ψ))) := by
  have h1 := two_form_sq_add_le n (fun j k => (c : ℂ) * σx j k) (wedge a b)
  have h2 := two_form_sq_smul n (c : ℂ) σx
  have h3 := two_form_sq_wedge_le n a b
  rw [ha, hb] at h3
  have hc2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  have hs0 := two_form_sq_nonneg n σx
  have hcs := mul_le_mul_of_nonneg_right hc2 hs0
  have hf0 : 0 ≤ fx2 := by
    rw [← hb]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD' : D * fx2 ≤ Real.exp ψ * fx2 := mul_le_mul_of_nonneg_right hD hf0
  have hE : 0 < Real.exp (-ph) := Real.exp_pos _
  have hQ : Real.exp (-ph) * Real.exp ψ = Real.exp (-(ph - ψ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) ≤
      2 * sq2 n σx + 4 * (Real.exp ψ * fx2) := by
    linarith
  calc sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) * Real.exp (-ph)
      ≤ (2 * sq2 n σx + 4 * (Real.exp ψ * fx2)) * Real.exp (-ph) :=
        mul_le_mul_of_nonneg_right hbound hE.le
    _ = 2 * (sq2 n σx * Real.exp (-ph)) + 4 * (fx2 * Real.exp (-(ph - ψ))) := by
        rw [← hQ]
        ring

theorem cut_S_bound {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ)
    (fx : V n) (x : M) :
    ‖∑ j, d n z j (fun y => (η y : ℂ)) x * fx j‖ ^ 2 ≤ dbarSq n z (fun y => (η y : ℂ)) x * ‖fx‖ ^ 2 := by
  have h := cut_cs n (fun j => d n z j (fun y => (η y : ℂ)) x) (fun j => fx j)
  unfold dbarSq
  rw [EuclideanSpace.norm_sq_eq]
  have he : ∑ j, ‖d n z j (fun y => (η y : ℂ)) x‖ ^ 2 =
      ∑ j, ‖db n z j (fun y => (η y : ℂ)) x‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [cut_norm_d_eq]
  rw [← he]
  exact h

theorem continuous_two_form_sq (n : ℕ) : Continuous (sq2 n) := by
  show Continuous fun σ : Fin n → Fin n → ℂ => sq2 n σ
  simp only [sq2]
  first
  | fun_prop
  | exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp (continuous_apply j)).norm.pow 2).div_const _

theorem cut_aem {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [NormedAddCommGroup E] (μ : Measure M) (u : M → E)
    (hu : AEStronglyMeasurable u μ) (ph : M → ℝ) (hph : Continuous ph) :
    AEMeasurable (fun x => ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x))) μ := by
  have h1 : AEMeasurable (fun x => ‖u x‖) μ := hu.norm.aemeasurable
  have h2 : Measurable (fun x => Real.exp (-ph x)) := (Real.continuous_exp.comp hph.neg).measurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.pow_const 2).mul h2.aemeasurable)

theorem aemeasurable_weighted_two_form {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (μ : Measure M) (u : M → Fin n → Fin n → ℂ)
    (hu : AEStronglyMeasurable u μ) (ph : M → ℝ) (hph : Continuous ph) :
    AEMeasurable (fun x => ENNReal.ofReal (sq2 n (u x) * Real.exp (-ph x))) μ := by
  have h1 : AEMeasurable (fun x => sq2 n (u x)) μ :=
    ((continuous_two_form_sq n).comp_aestronglyMeasurable hu).aemeasurable
  have h2 : Measurable (fun x => Real.exp (-ph x)) := (Real.continuous_exp.comp hph.neg).measurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.mul h2.aemeasurable)

private lemma continuous_coord_apply {n : ℕ} (j : Fin n) : Continuous (fun v : V n => v j) := by
  first
  | fun_prop
  | continuity
  | exact (EuclideanSpace.proj j).continuous
  | exact continuous_apply j

theorem cut_aesmW {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (μ : Measure M) (ph ψ η c : M → ℝ) (f : M → V n) (w : M → ℂ)
    (hc : Continuous c) (hE : Continuous (fun x => w1 ph ψ x - w2 ph ψ x))
    (hd : ∀ j, Continuous (d n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun x => (c x : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) μ := by
  have h1 : AEStronglyMeasurable (fun x => (c x : ℂ) * w x) μ :=
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hw
  have h2 : AEStronglyMeasurable (fun x => (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hE)).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) μ := by
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin n)), AEStronglyMeasurable
        (fun x => d n z j (fun y => (η y : ℂ)) x * f x j) μ := fun j _ =>
      (hd j).aestronglyMeasurable.mul ((continuous_coord_apply j).comp_aestronglyMeasurable hf)
    first
    | exact Finset.aestronglyMeasurable_sum' _ hj
    | exact Finset.aestronglyMeasurable_fun_sum _ hj
    | exact (Finset.aestronglyMeasurable_sum _ hj).congr (ae_of_all _ fun x => by simp)
  exact h1.sub (h2.mul h3)

theorem cut_aesmS {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (μ : Measure M) (η c : M → ℝ) (f : M → V n)
    (σ : M → Fin n → Fin n → ℂ) (hc : Continuous c)
    (hd : ∀ j, Continuous (db n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hσ : AEStronglyMeasurable σ μ) :
    AEStronglyMeasurable (fun x => fun j k => (c x : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k) μ := by
  have ha : Continuous (fun x => fun i => db n z i (fun y => (η y : ℂ)) x) :=
    continuous_pi fun i => hd i
  have hb : AEStronglyMeasurable (fun x => fun i => f x i) μ :=
    (continuous_pi fun i => continuous_coord_apply (n := n) i).comp_aestronglyMeasurable hf
  have hW : Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => wedge p.1 p.2) := by
    show Continuous fun p : (Fin n → ℂ) × (Fin n → ℂ) => fun j k => p.1 j * p.2 k - p.1 k * p.2 j
    first
    | fun_prop
    | exact continuous_pi fun j => continuous_pi fun k =>
        (((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub
          (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hpair : AEStronglyMeasurable
      (fun x => ((fun i => db n z i (fun y => (η y : ℂ)) x), (fun i => f x i))) μ := by
    first
    | exact ha.aestronglyMeasurable.prodMk hb
    | exact ha.aestronglyMeasurable.prod_mk hb
  have h2 : AEStronglyMeasurable
      (fun x => wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i)) μ :=
    hW.comp_aestronglyMeasurable hpair
  have h1 : AEStronglyMeasurable (fun x => (c x : ℂ) • σ x) μ :=
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.smul hσ
  first
  | exact h1.add h2
  | exact (h1.add h2).congr (ae_of_all _ fun x => by funext j k; simp)

end

end ReciprocityTheory.L2DbarEstimates.F

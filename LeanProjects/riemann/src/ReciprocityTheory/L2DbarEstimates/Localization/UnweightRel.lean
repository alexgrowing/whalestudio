import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section UnweightRelAux

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

lemma uwr_amgm (A B p : ℝ) : A * B ≤ A ^ 2 * Real.exp (-p) + B ^ 2 * Real.exp p := by
  rw [Real.exp_neg]
  have he := Real.exp_pos p
  have key : 0 ≤ A ^ 2 + B ^ 2 * Real.exp p ^ 2 - A * B * Real.exp p := by
    nlinarith [sq_nonneg (A - B * Real.exp p / 2), sq_nonneg (B * Real.exp p)]
  have h2 : A ^ 2 * (Real.exp p)⁻¹ + B ^ 2 * Real.exp p - A * B
      = (A ^ 2 + B ^ 2 * Real.exp p ^ 2 - A * B * Real.exp p) / Real.exp p := by
    field_simp
  have h3 := div_nonneg key he.le
  linarith

lemma sqNorm_entry_le_two_mul (σ : Fin n → Fin n → ℂ) (j k : Fin n) : ‖σ j k‖ ^ 2 ≤ 2 * sq2 n σ := by
  unfold sq2
  have e : 2 * ((∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2) = ∑ j, ∑ k, ‖σ j k‖ ^ 2 := by ring
  rw [e]
  calc ‖σ j k‖ ^ 2 ≤ ∑ k', ‖σ j k'‖ ^ 2 :=
        Finset.single_le_sum (f := fun k' => ‖σ j k'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', ‖σ j' k'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ k', ‖σ j' k'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)

lemma norm_sq_le_two_mul_sqNorm (σ : Fin n → Fin n → ℂ) : ‖σ‖ ^ 2 ≤ 2 * sq2 n σ := by
  have h0 : 0 ≤ 2 * sq2 n σ := by
    unfold sq2
    positivity
  have hb : ‖σ‖ ≤ Real.sqrt (2 * sq2 n σ) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    simpa using Real.abs_le_sqrt (sqNorm_entry_le_two_mul σ j k)
  calc ‖σ‖ ^ 2 ≤ (Real.sqrt (2 * sq2 n σ)) ^ 2 := by gcongr
    _ = 2 * sq2 n σ := Real.sq_sqrt h0

lemma uwr_contR (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hz' := hz
  unfold IsLocalHomeomorph at hz'
  unfold SmoothR Smooth at hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, rfl⟩ := hz' x
  have h1 := hf e (fun _ _ => rfl)
  have h2 : ContinuousAt ((fun y => (f y : ℂ)) ∘ e.symm) (e x) :=
    h1.continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h3 : ContinuousAt (fun y => (f y : ℂ)) x := by
    refine (h2.comp (e.continuousAt hx)).congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h4 : ContinuousAt (fun y => ((f y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4

lemma smoothR_secondWeight (ph ψ : M → ℝ) (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    SmoothR n z (w2 ph ψ) := by
  unfold SmoothR Smooth at *
  intro e he
  refine ((hph e he).sub (hψ e he)).congr fun y _ => ?_
  simp [w2]

lemma smoothR_firstWeight (ph ψ : M → ℝ) (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    SmoothR n z (w1 ph ψ) := by
  unfold SmoothR Smooth at *
  intro e he
  refine ((hph e he).sub ((contDiffOn_const (c := (2 : ℂ))).mul (hψ e he))).congr fun y _ => ?_
  simp [w1]

lemma uwr_fin_comp (f : M → V n) (p : M → ℝ) (hf : nV n z f p < ⊤) (k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖f x k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by
  unfold nV at hf
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
  have hk : ‖(f x) k‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.single_le_sum (f := fun i => ‖(f x) i‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ k)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)

lemma lintegral_weighted_entry_lt_top (σ : M → Fin n → Fin n → ℂ) (p : M → ℝ) (hσ : n2 n z σ p < ⊤) (j k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖σ x j k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by
  unfold n2 at hσ
  have h2 : ∫⁻ x, ENNReal.ofReal (2 * (sq2 n (σ x) * Real.exp (-p x))) ∂vol n z < ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hσ
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) h2
  apply ENNReal.ofReal_le_ofReal
  have h1 := sqNorm_entry_le_two_mul (σ x) j k
  have he := (Real.exp_pos (-p x)).le
  nlinarith

lemma uwr_integrable (hz : IsLocalHomeomorph z) (u h : M → ℂ) (p : M → ℝ) (hp : Continuous p)
    (hu : AEStronglyMeasurable u (vol n z))
    (hfin : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x => u x * h x) (vol n z) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hcont : Continuous (fun x => ‖h x‖ ^ 2 * Real.exp (p x)) :=
    (hh.norm.pow 2).mul (Real.continuous_exp.comp hp)
  have hcs : HasCompactSupport (fun x => ‖h x‖ ^ 2 * Real.exp (p x)) :=
    (hc.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)).mul_right
  have hI := hcont.integrable_of_hasCompactSupport (μ := vol n z) hcs
  have h2 : ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (p x)) ∂vol n z < ⊤ :=
    hI.lintegral_lt_top
  refine ⟨hu.mul hh.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖u x * h x‖ₑ ∂vol n z < ⊤
  calc ∫⁻ x, ‖u x * h x‖ₑ ∂vol n z
      ≤ ∫⁻ x, (ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-p x)) +
          ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (p x))) ∂vol n z := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_add (by positivity) (by positivity), norm_mul]
        exact ENNReal.ofReal_le_ofReal (uwr_amgm ‖u x‖ ‖h x‖ (p x))
    _ = _ := lintegral_add_right' _ hcont.measurable.ennreal_ofReal.aemeasurable
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfin, h2⟩

lemma locL2_of_sq_le_integrable_sum {E : Type*} [NormedAddCommGroup E] (u : M → E)
    (hu : AEStronglyMeasurable u (vol n z))
    (c F1 F2 : M → ℝ) (hc : Continuous c) (hF1 : ∀ x, 0 ≤ F1 x) (hF2 : ∀ x, 0 ≤ F2 x)
    (hF1m : AEMeasurable (fun x => ENNReal.ofReal (F1 x)) (vol n z))
    (hI1 : ∫⁻ x, ENNReal.ofReal (F1 x) ∂vol n z < ⊤)
    (hI2 : ∫⁻ x, ENNReal.ofReal (F2 x) ∂vol n z < ⊤)
    (hb : ∀ x, ‖u x‖ ^ 2 ≤ c x * (F1 x + F2 x)) : LocalL2Isometry (vol n z) u := by
  refine ⟨hu, fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hC.bddAbove_image hc.continuousOn
  have hK' : ∀ x ∈ C, c x ≤ max K 0 := fun x hx =>
    (hK (Set.mem_image_of_mem c hx)).trans (le_max_left _ _)
  calc ∫⁻ x in C, ‖u x‖ₑ ^ 2 ∂vol n z
      ≤ ∫⁻ x in C, ENNReal.ofReal (max K 0) * (ENNReal.ofReal (F1 x) + ENNReal.ofReal (F2 x))
          ∂vol n z := by
        refine setLIntegral_mono' hC.measurableSet fun x hx => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_add (hF1 x) (hF2 x), ← ENNReal.ofReal_mul (le_max_right _ _)]
        apply ENNReal.ofReal_le_ofReal
        calc ‖u x‖ ^ 2 ≤ c x * (F1 x + F2 x) := hb x
          _ ≤ max K 0 * (F1 x + F2 x) :=
            mul_le_mul_of_nonneg_right (hK' x hx) (add_nonneg (hF1 x) (hF2 x))
    _ ≤ ∫⁻ x, ENNReal.ofReal (max K 0) * (ENNReal.ofReal (F1 x) + ENNReal.ofReal (F2 x))
          ∂vol n z := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (max K 0) *
          (∫⁻ x, ENNReal.ofReal (F1 x) ∂vol n z + ∫⁻ x, ENNReal.ofReal (F2 x) ∂vol n z) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hF1m]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hI1, hI2⟩)

lemma uwr_boundS (E s t α q P N : ℝ) (hE : 0 < E) (hq : 0 ≤ q)
    (hsq : s ^ 2 ≤ 2 * q) (hN0 : 0 ≤ N) (hN : N ≤ E * (s + 2 * α * t)) :
    N ^ 2 ≤ (4 * E ^ 2 * Real.exp P + 8 * E * α ^ 2) * (q * Real.exp (-P) + t ^ 2 * E) := by
  have hP : Real.exp P * Real.exp (-P) = 1 := by
    rw [← Real.exp_add]
    simp
  have hEP := Real.exp_pos P
  have hEm := Real.exp_pos (-P)
  have h1 : N ^ 2 ≤ (E * (s + 2 * α * t)) ^ 2 := by nlinarith
  have h2 : (s + 2 * α * t) ^ 2 ≤ 4 * q + 8 * α ^ 2 * t ^ 2 := by
    nlinarith [sq_nonneg (s - 2 * α * t)]
  have h3 : N ^ 2 ≤ E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) := by
    calc N ^ 2 ≤ (E * (s + 2 * α * t)) ^ 2 := h1
      _ = E ^ 2 * (s + 2 * α * t) ^ 2 := by ring
      _ ≤ E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) := by gcongr
  have e1 : 0 ≤ 4 * E ^ 3 * t ^ 2 * Real.exp P := by positivity
  have e2 : 0 ≤ 8 * E * α ^ 2 * q * Real.exp (-P) := by positivity
  have key : (4 * E ^ 2 * Real.exp P + 8 * E * α ^ 2) * (q * Real.exp (-P) + t ^ 2 * E)
      = E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) + 4 * E ^ 3 * t ^ 2 * Real.exp P +
        8 * E * α ^ 2 * q * Real.exp (-P) := by
    linear_combination (4 * E ^ 2 * q) * hP
  rw [key]
  linarith

end UnweightRelAux

theorem unweightRel (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : UnweightRelStatement n M := by
  intro z hz ph ψ f w σ hph hψ hf hw hσ hA hS
  have ha : SmoothR n z (w2 ph ψ) := smoothR_secondWeight ph ψ hph hψ
  have hb : SmoothR n z (w1 ph ψ) := smoothR_firstWeight ph ψ hph hψ
  have hac : Continuous (w2 ph ψ) := uwr_contR hz _ ha
  have hbc : Continuous (w1 ph ψ) := uwr_contR hz _ hb
  have hphc : Continuous ph := uwr_contR hz _ hph
  have hEc : Continuous fun x => Real.exp (-w2 ph ψ x) := by fun_prop
  have hE1c : Continuous fun x => Real.exp (-w1 ph ψ x) := by fun_prop
  have hαc : ∀ i, Continuous (db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ))) := fun i =>
    Smooth.continuous n z hz _ (Smooth.db n z i _ ha)
  have hαvc : Continuous fun x => (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) :=
    continuous_pi hαc

  have hGm : AEStronglyMeasurable (unwG ph ψ f) (vol n z) :=
    (Complex.continuous_ofReal.comp hEc).aestronglyMeasurable.smul hf.1
  have hDm : AEStronglyMeasurable (unwD ph ψ w) (vol n z) :=
    ((Complex.continuous_ofReal.comp hE1c).aestronglyMeasurable.mul hw.1).neg
  have hSm : AEStronglyMeasurable (unwS n z ph ψ f σ) (vol n z) := by
    have hΦ : Continuous (fun p : ℝ × (Fin n → Fin n → ℂ) × (Fin n → ℂ) × V n =>
        fun j k => (p.1 : ℂ) * (p.2.1 j k - wedge p.2.2.1 (fun i => p.2.2.2 i) j k)) := by
      unfold wedge; fun_prop
    exact hΦ.comp_aestronglyMeasurable
      (hEc.aestronglyMeasurable.prodMk (hσ.1.prodMk (hαvc.aestronglyMeasurable.prodMk hf.1)))
  have hsq2c : Continuous (sq2 n) := by unfold sq2; fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine locL2_of_sq_le_integrable_sum _ hGm (fun x => Real.exp (-w2 ph ψ x))
      (fun x => ‖f x‖ ^ 2 * Real.exp (-w2 ph ψ x)) (fun _ => 0) hEc (fun x => by positivity)
      (fun _ => le_rfl) ((hf.1.norm.pow 2).mul hEc.aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hf.2 (by simp) (fun x => le_of_eq ?_)
    simp only [unwG, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    ring
  ·
    refine locL2_of_sq_le_integrable_sum _ hDm (fun x => Real.exp (-w1 ph ψ x))
      (fun x => ‖w x‖ ^ 2 * Real.exp (-w1 ph ψ x)) (fun _ => 0) hE1c (fun x => by positivity)
      (fun _ => le_rfl) ((hw.1.norm.pow 2).mul hE1c.aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hw.2 (by simp) (fun x => le_of_eq ?_)
    simp only [unwD, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    ring
  ·
    have hN : ∀ x, ‖unwS n z ph ψ f σ x‖ ≤ Real.exp (-w2 ph ψ x) *
        (‖σ x‖ + 2 * ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ * ‖f x‖) := by
      intro x
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j =>
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      have e1 : ‖σ x j k‖ ≤ ‖σ x‖ := (norm_le_pi_norm (σ x j) k).trans (norm_le_pi_norm (σ x) j)
      have e2 : ∀ i, ‖db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ≤
          ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ := fun i =>
        norm_le_pi_norm (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) i
      have e3 : ∀ i, ‖f x i‖ ≤ ‖f x‖ := fun i => PiLp.norm_apply_le (f x) i
      have p1 := mul_le_mul (e2 j) (e3 k) (norm_nonneg _) (norm_nonneg _)
      have p2 := mul_le_mul (e2 k) (e3 j) (norm_nonneg _) (norm_nonneg _)
      simp only [unwS, wedge, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine (norm_sub_le _ _).trans ?_
      have p3 := norm_sub_le (db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * f x k)
        (db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * f x j)
      rw [norm_mul, norm_mul] at p3
      linarith
    refine locL2_of_sq_le_integrable_sum _ hSm (fun x => 4 * Real.exp (-w2 ph ψ x) ^ 2 * Real.exp (ph x) +
        8 * Real.exp (-w2 ph ψ x) * ‖(fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)‖ ^ 2)
      (fun x => sq2 n (σ x) * Real.exp (-ph x)) (fun x => ‖f x‖ ^ 2 * Real.exp (-w2 ph ψ x))
      (by fun_prop) (fun x => mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le)
      (fun x => by positivity)
      ((hsq2c.comp_aestronglyMeasurable hσ.1).mul
        (by fun_prop : Continuous fun x => Real.exp (-ph x)).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      hσ.2 hf.2 (fun x => ?_)
    exact uwr_boundS _ _ _ _ _ _ _ (Real.exp_pos _) (by unfold sq2; positivity) (norm_sq_le_two_mul_sqNorm _)
      (norm_nonneg _) (hN x)
  ·
    intro φ hφ
    have hg : IsTest n z (fun x => conj (φ x)) :=
      ⟨Smooth.conj n z φ hφ.1, hφ.2.comp_left (map_zero _)⟩
    have h := hA _ hg
    have e1 : ∀ x, ∑ j, unwG ph ψ f x j * d n z j φ x =
        ⟪dbarF n z (fun x => conj (φ x)) x, f x⟫_ℂ * (Real.exp (-w2 ph ψ x) : ℂ) := by
      intro x
      simp only [dbarF, PiLp.inner_apply, RCLike.inner_apply', db_conj,
        Complex.conj_conj, unwG, PiLp.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∀ x, conj (conj (φ x)) * w x * (Real.exp (-w1 ph ψ x) : ℂ) =
        -(unwD ph ψ w x * φ x) := by
      intro x; simp only [unwD, Complex.conj_conj]; ring
    calc ∫ x, ∑ j, unwG ph ψ f x j * d n z j φ x ∂vol n z
        = ∫ x, ⟪dbarF n z (fun x => conj (φ x)) x, f x⟫_ℂ * (Real.exp (-w2 ph ψ x) : ℂ)
            ∂vol n z := integral_congr_ae (ae_of_all _ e1)
      _ = ∫ x, conj (conj (φ x)) * w x * (Real.exp (-w1 ph ψ x) : ℂ) ∂vol n z := h
      _ = ∫ x, -(unwD ph ψ w x * φ x) ∂vol n z := integral_congr_ae (ae_of_all _ e2)
      _ = -∫ x, unwD ph ψ w x * φ x ∂vol n z := integral_neg _
  ·
    intro φ hφ j k
    have hk : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) := Real.contDiff_exp.comp contDiff_neg
    have hE : Smooth n z (fun x => ((Real.exp (-w2 ph ψ x) : ℝ) : ℂ)) :=
      SmoothR.comp n z _ hk _ ha
    set φ' : M → ℂ := fun x => ((Real.exp (-w2 ph ψ x) : ℝ) : ℂ) * φ x with hφ'def
    have hφ' : IsTest n z φ' :=
      ⟨Smooth.mul n z _ _ hE hφ.1, hφ.2.mono (fun x hx h0 => hx (by simp [hφ'def, h0]))⟩
    have hderiv : ∀ s : ℝ, deriv (fun t : ℝ => Real.exp (-t)) s = -Real.exp (-s) := by
      intro s; rw [((hasDerivAt_neg s).exp).deriv]; ring
    have hder : ∀ i x, db n z i φ' x =
        -((Real.exp (-w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) * φ x +
          (Real.exp (-w2 ph ψ x) : ℂ) * db n z i φ x := by
      intro i x
      rw [hφ'def, db_mul n z _ _ (Smooth.ck n z 1 _ hE) (Smooth.ck n z 1 _ hφ.1)]
      have hc := db_comp_real n z (fun t => Real.exp (-t)) hk (w2 ph ψ) (SmoothR.ckR n z 1 _ ha) i x
      rw [hc, hderiv]; push_cast; ring
    have hφc : Continuous φ := Smooth.continuous n z hz _ hφ.1
    have hfk : ∀ i, AEStronglyMeasurable (fun x => f x i) (vol n z) := fun i =>
      (by fun_prop : Continuous fun v : V n => v i).comp_aestronglyMeasurable hf.1
    have hIf : ∀ (i : Fin n) (h : M → ℂ), Continuous h → HasCompactSupport h →
        Integrable (fun x => f x i * h x) (vol n z) := fun i h h1 h2 =>
      uwr_integrable hz _ h _ hac (hfk i) (uwr_fin_comp f _ hf.2 i) h1 h2
    have hdbφ' : ∀ i, Continuous (db n z i φ') ∧ HasCompactSupport (db n z i φ') := fun i =>
      ⟨Smooth.continuous n z hz _ (Smooth.db n z i _ hφ'.1),
        hφ'.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ'))⟩
    have hWi : ∀ i, Continuous (fun x => (Real.exp (-w2 ph ψ x) : ℂ) * φ x *
          db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) ∧
        HasCompactSupport (fun x => (Real.exp (-w2 ph ψ x) : ℂ) * φ x *
          db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) := fun i =>
      ⟨by have := hαc i; fun_prop, hφ.2.mono (fun x hx h0 => hx (by simp [h0]))⟩
    have hIA : Integrable (fun x => f x k * db n z j φ' x - f x j * db n z k φ' x) (vol n z) :=
      (hIf k _ (hdbφ' j).1 (hdbφ' j).2).sub (hIf j _ (hdbφ' k).1 (hdbφ' k).2)
    have hIW : Integrable (fun x =>
        f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
        f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x))
        (vol n z) :=
      (hIf k _ (hWi j).1 (hWi j).2).sub (hIf j _ (hWi k).1 (hWi k).2)
    have hIσ : Integrable (fun x => σ x j k * φ' x) (vol n z) :=
      uwr_integrable hz _ φ' ph hphc
        ((by fun_prop : Continuous fun s : Fin n → Fin n → ℂ => s j k).comp_aestronglyMeasurable hσ.1)
        (lintegral_weighted_entry_lt_top σ ph hσ.2 j k) (Smooth.continuous n z hz _ hφ'.1) hφ'.2
    have hmain := hS φ' hφ' j k
    have hT : ∀ x, unwG ph ψ f x k * db n z j φ x - unwG ph ψ f x j * db n z k φ x =
        (f x k * db n z j φ' x - f x j * db n z k φ' x) +
        (f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
         f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)) := by
      intro x; rw [hder, hder]; simp only [unwG, PiLp.smul_apply, smul_eq_mul]; ring
    have hU : ∀ x, σ x j k * φ' x -
        (f x k * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) -
         f x j * ((Real.exp (-w2 ph ψ x) : ℂ) * φ x * db n z k (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)) =
        unwS n z ph ψ f σ x j k * φ x := by
      intro x; simp only [hφ'def, unwS, wedge]; ring
    rw [integral_congr_ae (ae_of_all _ hT), integral_add hIA hIW, hmain,
      ← integral_congr_ae (ae_of_all _ hU), integral_sub hIσ hIW]
    ring
  ·
    intro hfc
    exact hfc.mono (fun x hx h0 => hx (by simp [unwG, h0]))
  ·
    intro hwc
    exact hwc.mono (fun x hx h0 => hx (by simp [unwD, h0]))
  ·
    intro hfc hσc
    refine IsCompact.of_isClosed_subset (hfc.isCompact.union hσc.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hno
    simp only [mem_union, not_or] at hno
    apply hx
    have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport hno.1
    have h2 : σ x = 0 := image_eq_zero_of_notMem_tsupport hno.2
    funext j k
    simp [unwS, wedge, h1, h2]

end

end ReciprocityTheory.L2DbarEstimates.F

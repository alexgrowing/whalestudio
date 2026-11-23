import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCompactSecondCountable

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot MeasureTheory
open GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex GlobalTheory.LineUMod

noncomputable section
namespace GlobalTheory.CompanionTheory.SwapInt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul_of_ne {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have h := v_eq_exp' (mul_ne_zero hx hy)
  rw [map_mul, v_eq_exp' hx, v_eq_exp' hy, ← WithZero.exp_add] at h
  have := WithZero.exp_injective h
  omega

theorem v_le_exp_iff {x : L} (hx : x ≠ 0) (k : ℤ) : Valued.v x ≤ WithZero.exp (-k) ↔ k ≤ ordL x := by
  rw [v_eq_exp' hx, WithZero.exp_le_exp]; omega

theorem ordL_eq_of_v_eq {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) (h : Valued.v x = Valued.v y) :
    ordL x = ordL y := by
  rw [v_eq_exp' hx, v_eq_exp' hy] at h
  have := WithZero.exp_injective h
  omega

theorem isAdm_add_right {w : ℂ} {F : L → ℂ} (hF : IsAdm w F) (y : L) : IsAdm w (fun x => F (x + y)) := by
  obtain ⟨h1, R, C, h2⟩ := hF
  refine ⟨h1.comp_continuous (continuous_id.add continuous_const), ?_⟩
  by_cases hy : y = 0
  · subst hy
    exact ⟨R, C, fun x hx hr => by simpa using h2 x hx hr⟩
  refine ⟨min R (ordL y - 1), C, fun x hx hr => ?_⟩
  have hr1 := hr.trans (min_le_left _ _)
  have hr2 := hr.trans (min_le_right _ _)
  have hlt : Valued.v y < Valued.v x := by
    rw [v_eq_exp' hx, v_eq_exp' hy, WithZero.exp_lt_exp]; omega
  have hv : Valued.v (x + y) = Valued.v x := Valuation.map_add_eq_of_lt_left _ hlt
  have hne : x + y ≠ 0 := by
    intro e
    rw [e, map_zero] at hv
    exact hx ((map_eq_zero _).1 hv.symm)
  have ho := ordL_eq_of_v_eq hne hx hv
  show F (x + y) = _
  rw [h2 _ hne (by omega), ho]

theorem isAdm_mul_left {w : ℂ} (hw : w ≠ 0) {F : L → ℂ} (hF : IsAdm w F) {c : L} (hc : c ≠ 0) :
    IsAdm w (fun x => F (c * x)) := by
  obtain ⟨h1, R, C, h2⟩ := hF
  refine ⟨h1.comp_continuous (continuous_const.mul continuous_id), R - ordL c, C * w ^ (-ordL c),
    fun x hx hr => ?_⟩
  have ho := ordL_mul_of_ne hc hx
  show F (c * x) = _
  rw [h2 _ (mul_ne_zero hc hx) (by omega), ho, neg_add, zpow_add₀ hw, mul_assoc]

theorem sphFn_of_le {w : ℂ} {x : L} (hx : Valued.v x ≤ 1) : sphFn w x = 1 := if_pos hx

theorem sphFn_of_lt {w : ℂ} {x : L} (hx : ¬ Valued.v x ≤ 1) : sphFn w x = w ^ (-ordL x) := if_neg hx

theorem isLocallyConstant_sphFn {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (w : ℂ) :
    IsLocallyConstant (sphFn (L := L) w) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : Valued.v x ≤ 1
  · have : {y : L | Valued.v y ≤ 1} ∈ nhds x := (Valued.isOpen_integer L).mem_nhds hx
    filter_upwards [this] with y hy
    rw [sphFn_of_le hx, sphFn_of_le hy]
  · have h0 : Valued.v x ≠ 0 := fun e => hx (by rw [e]; exact zero_le')
    have hx0 : x ≠ 0 := (map_ne_zero _).1 h0
    have ho : IsOpen ((fun y => y - x) ⁻¹' {z : L | Valued.v z ≤ WithZero.exp (-(ordL x + 1))}) :=
      (isOpen_vball hϖ (ordL x + 1)).preimage (continuous_id.sub continuous_const)
    have hm : x ∈ (fun y => y - x) ⁻¹' {z : L | Valued.v z ≤ WithZero.exp (-(ordL x + 1))} := by
      simp
    filter_upwards [ho.mem_nhds hm] with y hy
    have hy' : Valued.v y = Valued.v x := by
      have hlt : Valued.v (y - x) < Valued.v x := by
        refine lt_of_le_of_lt hy ?_
        rw [v_eq_exp' hx0, WithZero.exp_lt_exp]; omega
      have := Valuation.map_add_eq_of_lt_left (Valued.v : Valuation L _) hlt
      rwa [add_sub_cancel] at this
    have hy0 : y ≠ 0 := (map_ne_zero (Valued.v : Valuation L _)).1 (hy' ▸ h0)
    rw [sphFn_of_lt hx, sphFn_of_lt (hy' ▸ hx), ordL_eq_of_v_eq hy0 hx0 hy']

theorem isAdm_sphFn {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (w : ℂ) :
    IsAdm w (sphFn (L := L) w) := by
  refine ⟨isLocallyConstant_sphFn hϖ w, -1, 1, fun x hx hr => ?_⟩
  have : ¬ Valued.v x ≤ 1 := by
    have := v_le_exp_iff hx 0
    rw [neg_zero, WithZero.exp_zero] at this
    rw [this]; omega
  rw [sphFn_of_lt this, one_mul]

section Meas

variable [CompleteSpace L] [LocallyCompactSpace L] [SecondCountableTopology L]
  [MeasurableSpace L] [BorelSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem real_ordBall_neg (h : IsUnramInv ϖ σ q) (μ : Measure L) [μ.IsAddHaarMeasure] (n : ℕ) :
    μ.real (ordBall L (-(n : ℤ))) = ((q : ℝ) ^ 2) ^ n * μ.real (ordBall L 0) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hk : -(n : ℤ) ≤ 0 := by omega
  have e := relIndex_ordBall h hk
  haveI : ((ordBall L 0).addSubgroupOf (ordBall L (-(n : ℤ)))).FiniteIndex :=
    ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
  have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L 0) (ordBall L (-(n : ℤ))) (ordBall_mono hk)
    (isOpen_vball h.2.2.2.1 0).measurableSet μ
  have e2 : (0 - -(n : ℤ)).toNat = n := by omega
  rw [Measure.real, ← this, e, e2, ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_pow,
    Measure.real]

theorem map_mul_left_eq (h : IsUnramInv ϖ σ q) (μ : Measure L) [μ.IsAddHaarMeasure] [μ.Regular]
    {c : L} (hc : c ≠ 0) :
    μ.map (fun x => c * x) = ((distribHaarChar L (Units.mk0 c hc)⁻¹ : NNReal) : ENNReal) • μ := by
  have hm : Measurable fun x : L => c * x := (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul, distribHaarChar_mul]
  congr 1
  ext x
  simp [Set.mem_inv_smul_set_iff, Units.smul_def]

theorem integral_comp_mul_left (h : IsUnramInv ϖ σ q) (μ : Measure L) [μ.IsAddHaarMeasure] [μ.Regular]
    (F : L → ℂ) {c : L} (hc : c ≠ 0) :
    ∫ x, F (c * x) ∂μ = (q : ℂ) ^ (2 * ordL c) * ∫ x, F x ∂μ := by
  have hq : (q : ℝ) ≠ 0 := by
    have := h.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have h1 := (Homeomorph.mulLeft₀ c hc).measurableEmbedding.integral_map (μ := μ) F
  have e : ⇑(Homeomorph.mulLeft₀ c hc) = fun x => c * x := rfl
  rw [e] at h1
  rw [← h1, map_mul_left_eq h μ hc, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  have h2 := distribHaarChar_eq h (Units.mk0 c hc)⁻¹
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, ordL_inv' hc] at h2
  rw [h2, Complex.ofReal_zpow, Complex.ofReal_natCast]
  congr 2
  ring

theorem integrable_sphFn (h : IsUnramInv ϖ σ q) (μ : Measure L) [μ.IsAddHaarMeasure]
    (hμ : μ.real (ordBall L 0) = 1) {w : ℂ} (hw : ‖w‖ * (q : ℝ) ^ 2 < 1) :
    Integrable (sphFn (L := L) w) μ := by
  have hf : Continuous (sphFn (L := L) w) := (isLocallyConstant_sphFn h.2.2.2.1 w).continuous
  have hbm : ∀ k : ℤ, MeasurableSet (ordBall L k : Set L) := fun k => (isOpen_vball h.2.2.2.1 k).measurableSet
  have hbi : ∀ k : ℤ, IntegrableOn (sphFn (L := L) w) (ordBall L k : Set L) μ := fun k =>
    hf.continuousOn.integrableOn_compact (isCompact_vball h k)
  let s : ℕ → Set L := fun n => (ordBall L (-((n + 1 : ℕ) : ℤ)) : Set L) \ (ordBall L (-(n : ℤ)) : Set L)
  have hsm : ∀ n, MeasurableSet (s n) := fun n => (hbm _).diff (hbm _)
  have hval : ∀ n, ∀ x ∈ s n, ‖sphFn w x‖ = ‖w‖ ^ (n + 1) := by
    rintro n x ⟨h1, h2⟩
    have hx0 : x ≠ 0 := fun e => h2 (e ▸ zero_mem (ordBall L (-(n : ℤ))))
    have h3 := (v_le_exp_iff hx0 _).1 (mem_ordBall.1 h1)
    have h4 : ¬ (-(n : ℤ) ≤ ordL x) := fun e => h2 (mem_ordBall.2 ((v_le_exp_iff hx0 _).2 e))
    have h5 : ¬ Valued.v x ≤ 1 := by
      have := v_le_exp_iff hx0 0
      rw [neg_zero, WithZero.exp_zero] at this
      rw [this]; omega
    have h6 : -ordL x = ((n + 1 : ℕ) : ℤ) := by omega
    rw [sphFn_of_lt h5, h6, zpow_natCast, norm_pow]
  have hint : ∀ n, ∫ x in s n, ‖sphFn w x‖ ∂μ ≤ (‖w‖ * (q : ℝ) ^ 2) ^ (n + 1) := by
    intro n
    rw [setIntegral_congr_fun (hsm n) (hval n), setIntegral_const, smul_eq_mul, mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : μ.real (s n) ≤ μ.real (ordBall L (-((n + 1 : ℕ) : ℤ))) :=
      measureReal_mono Set.diff_subset (isCompact_vball h _).measure_ne_top
    rwa [real_ordBall_neg h μ, hμ, mul_one] at h1
  have hsum : Summable fun n => ∫ x in s n, ‖sphFn w x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hint ?_
    exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity) hw)
  have hU : IntegrableOn (sphFn (L := L) w) (Set.iUnion s) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun n => (hbi _).mono_set Set.diff_subset) hsum
  have hcov : (ordBall L 0 : Set L) ∪ Set.iUnion s = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ (ordBall L 0 : Set L)
    · exact Or.inl hx
    · refine Or.inr (Set.mem_iUnion.2 ⟨(-ordL x - 1).toNat, ?_⟩)
      have hx0 : x ≠ 0 := fun e => hx (e ▸ zero_mem (ordBall L 0))
      have h1 : ¬ (0 ≤ ordL x) := fun e => hx (mem_ordBall.2 ((v_le_exp_iff hx0 _).2 e))
      refine ⟨mem_ordBall.2 ((v_le_exp_iff hx0 _).2 (by omega)), fun e => ?_⟩
      have := (v_le_exp_iff hx0 _).1 (mem_ordBall.1 e)
      omega
  have := (hbi 0).union hU
  rwa [hcov, integrableOn_univ] at this

theorem integrable_of_isAdm (h : IsUnramInv ϖ σ q) (μ : Measure L) [μ.IsAddHaarMeasure]
    (hμ : μ.real (ordBall L 0) = 1) {w : ℂ} (hw : ‖w‖ * (q : ℝ) ^ 2 < 1) {F : L → ℂ} (hF : IsAdm w F) :
    Integrable F μ := by
  obtain ⟨h1, R, C, h2⟩ := hF
  have hf : Continuous (sphFn (L := L) w) := (isLocallyConstant_sphFn h.2.2.2.1 w).continuous
  have hc : Continuous fun x => F x - C * sphFn w x := h1.continuous.sub (continuous_const.mul hf)
  have hcs : HasCompactSupport fun x => F x - C * sphFn w x := by
    refine HasCompactSupport.intro (isCompact_vball h (min R (-1) + 1)) fun x hx => ?_
    have hx0 : x ≠ 0 := fun e => hx (by simp [e])
    have h3 : ¬ (min R (-1) + 1 ≤ ordL x) := fun e => hx ((v_le_exp_iff hx0 _).2 e)
    have h4 : ordL x ≤ R := by
      have := min_le_left R (-1); omega
    have h5 : ordL x ≤ -1 := by
      have := min_le_right R (-1); omega
    have h6 : ¬ Valued.v x ≤ 1 := by
      have := v_le_exp_iff hx0 0
      rw [neg_zero, WithZero.exp_zero] at this
      rw [this]; omega
    rw [h2 x hx0 h4, sphFn_of_lt h6, sub_self]
  have := (hc.integrable_of_hasCompactSupport (μ := μ) hcs).add ((integrable_sphFn h μ hμ hw).const_mul C)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

end Meas

theorem sphFn_mul_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {w : ℂ} (hw : w ≠ 0) (x : L) :
    sphFn w (ϖ * x) = w⁻¹ * sphFn w x + (1 - w⁻¹) * (ordBall L 0 : Set L).indicator (fun _ => (1 : ℂ)) x := by
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have ho : ordL ϖ = 1 := by
    have := v_eq_exp' hϖ0
    rw [hϖ] at this
    have := WithZero.exp_injective this
    omega
  by_cases hx : Valued.v x ≤ 1
  · have h1 : Valued.v (ϖ * x) ≤ 1 := by
      rw [map_mul, hϖ]
      exact mul_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hx
    have h2 : x ∈ (ordBall L 0 : Set L) := by
      rw [SetLike.mem_coe, mem_ordBall, neg_zero, WithZero.exp_zero]; exact hx
    rw [sphFn_of_le h1, sphFn_of_le hx, Set.indicator_of_mem h2]
    ring
  · have hx0 : x ≠ 0 := fun e => hx (by simp [e])
    have h1 : ordL x < 0 := by
      have := v_le_exp_iff hx0 0
      rw [neg_zero, WithZero.exp_zero] at this
      rw [this] at hx; omega
    have h2 : x ∉ (ordBall L 0 : Set L) := fun e => hx (by
      rw [SetLike.mem_coe, mem_ordBall, neg_zero, WithZero.exp_zero] at e; exact e)
    have h3 := ordL_mul_of_ne hϖ0 hx0
    rw [sphFn_of_lt hx, Set.indicator_of_notMem h2, mul_zero, add_zero]
    have h4 : w⁻¹ * w ^ (-ordL x) = w ^ (-ordL (ϖ * x)) := by
      rw [h3, ho, neg_add, zpow_add₀ hw, zpow_neg_one]
    rw [h4]
    by_cases h5 : Valued.v (ϖ * x) ≤ 1
    · have h6 : ordL (ϖ * x) = 0 := by
        have := (v_le_exp_iff (mul_ne_zero hϖ0 hx0) 0)
        rw [neg_zero, WithZero.exp_zero] at this
        have := this.1 h5
        omega
      rw [sphFn_of_le h5, h6]; simp
    · rw [sphFn_of_lt h5]

theorem exists_invariant_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ w : ℂ, w ≠ 0 → ‖w‖ * (q : ℝ) ^ 2 < 1 →
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) := by
  intro L _ _ _ ϖ σ q h w hw0 hw
  obtain ⟨hlc, hsc⟩ := locCompact_secondCountable h
  borelize L
  let K : TopologicalSpace.PositiveCompacts L :=
    ⟨⟨(ordBall L 0 : Set L), isCompact_vball h 0⟩,
      ⟨0, mem_interior_iff_mem_nhds.2 ((isOpen_vball h.2.2.2.1 0).mem_nhds (zero_mem (ordBall L 0)))⟩⟩
  let μ : Measure L := Measure.addHaarMeasure K
  have hμ : μ.real (ordBall L 0) = 1 := by
    have : μ (ordBall L 0 : Set L) = 1 := Measure.addHaarMeasure_self (K₀ := K)
    simp [Measure.real, this]
  have hint : ∀ {F : L → ℂ}, IsAdm w F → Integrable F μ := fun hF => integrable_of_isAdm h μ hμ hw hF
  have hS := isAdm_sphFn (L := L) h.2.2.2.1 w
  refine ⟨fun F => ∫ x, F x ∂μ, fun F G hF hG => integral_add (hint hF) (hint hG), fun c F _ => ?_,
    fun F y hF => ⟨isAdm_add_right hF y, integral_add_right_eq_self F y⟩,
    fun F c hF hc => ⟨isAdm_mul_left hw0 hF hc, integral_comp_mul_left h μ F hc⟩, hS, ?_⟩
  · exact integral_const_mul c F
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := h.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have ho : ordL ϖ = 1 := by
    have := v_eq_exp' hϖ0
    rw [hϖ] at this
    have := WithZero.exp_injective this
    omega
  have h1 := integral_comp_mul_left h μ (sphFn w) hϖ0
  have hind : Integrable ((ordBall L 0 : Set L).indicator (fun _ => (1 : ℂ))) μ :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_vball h 0)).integrable_indicator
      (isOpen_vball h.2.2.2.1 0).measurableSet
  have h2 : ∫ x, (ordBall L 0 : Set L).indicator (fun _ => (1 : ℂ)) x ∂μ = 1 := by
    have hb : MeasurableSet (ordBall L 0 : Set L) := (isOpen_vball h.2.2.2.1 0).measurableSet
    rw [integral_indicator hb, setIntegral_const, hμ, one_smul]
  have h3 : ∫ x, sphFn w (ϖ * x) ∂μ = w⁻¹ * ∫ x, sphFn w x ∂μ + (1 - w⁻¹) := by
    simp_rw [sphFn_mul_uniformizer hϖ hw0]
    rw [integral_add ((hint hS).const_mul _) (hind.const_mul _), integral_const_mul, integral_const_mul, h2,
      mul_one]
  rw [h3, ho] at h1
  have hne : 1 - w * (q : ℂ) ^ 2 ≠ 0 := by
    intro e
    have : w * (q : ℂ) ^ 2 = 1 := by linear_combination -e
    have h4 := congrArg norm this
    rw [norm_mul, norm_pow, Complex.norm_natCast, norm_one] at h4
    exact hw.ne h4
  show ∫ x, sphFn w x ∂μ = _
  rw [eq_div_iff hne]
  have h5 : (q : ℂ) ^ (2 * (1 : ℤ)) = (q : ℂ) ^ 2 := by norm_cast
  rw [h5] at h1
  field_simp at h1
  linear_combination h1

end GlobalTheory.CompanionTheory.SwapInt

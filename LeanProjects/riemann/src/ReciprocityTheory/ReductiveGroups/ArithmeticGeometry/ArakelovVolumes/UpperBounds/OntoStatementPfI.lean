import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

theorem sq_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℂ} {k : α → ℝ}
    (hk : ∀ x, 0 < k x) {om : α → ℝ≥0∞}
    (ha : AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) μ) :
    ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ
      ≤ ∫⁻ x, (2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
          2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        have hk' := hk x
        have hA : 0 ≤ ‖a x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have hB : 0 ≤ ‖b x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have h1 : ‖a x + b x‖ ^ 2 / k x ≤ 2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          exact div_le_div_of_nonneg_right (sq_add_le _ _) hk'.le
        calc ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x
            ≤ ENNReal.ofReal (2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x)) * om x := by
              gcongr
          _ = 2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
                2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x) := by
              rw [ENNReal.ofReal_add (mul_nonneg zero_le_two hA) (mul_nonneg zero_le_two hB),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
              ring
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
        rw [lintegral_add_left' (ha.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem pnorm_sub_le (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  unfold Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _)
    (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem bdd_sub {la : Wt X.Ψ r} {f g : Frame X.Ψ r → ℂ} (hf : X.IsBddSec la f) (hg : X.IsBddSec la g) :
    X.IsBddSec la (fun y => f y - g y) := by
  obtain ⟨hf1, C1, hC1⟩ := hf
  obtain ⟨hg1, C2, hC2⟩ := hg
  refine ⟨?_, C1 + C2, fun x hx => (pnorm_sub_le X la f g x).trans (add_le_add (hC1 x hx) (hC2 x hx))⟩
  unfold Data.IsSec at hf1 hg1 ⊢
  obtain ⟨hd1, hb1, hl1⟩ := hf1
  obtain ⟨hd2, hb2, hl2⟩ := hg1
  refine ⟨hd1.sub hd2, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hb1 x hx b hb, hb2 x hx b hb]
    ring
  · simp only [hl1 γ hγ x hx, hl2 γ hγ x hx]
    ring

theorem poin_add (la : Wt X.Ψ r) {P1 P2 : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (h1 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P1 (lact γ.1 x)‖)
    (h2 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P2 (lact γ.1 x)‖) :
    poin X la (fun y => P1 y + P2 y) x = poin X la P1 x + poin X la P2 x := by
  unfold poin
  rw [← Summable.tsum_add h1.of_norm h2.of_norm]
  congr 1
  funext γ
  ring

theorem poin_smul (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    poin X la (fun y => a * P y) x = a * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  ring

theorem poin_zero (la : Wt X.Ψ r) (x : Frame X.Ψ r) : poin X la (fun _ => 0) x = 0 := by
  simp [poin]

variable (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))

def nuF : Measure (V (nd X)) :=
  ((muF X x0).restrict FF).withDensity fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal

variable {X x0 W FF}

private lemma measurable_cpt : Measurable (cpt X x0) := by
  refine measurable_pi_lambda _ fun τ => measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [cpt, rmul, mat, nmat, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs
  · refine Measurable.const_mul ?_ _
    first
      | exact measurable_pi_apply _
      | exact (EuclideanSpace.proj _).continuous.measurable
      | fun_prop
  · exact measurable_const
  · exact measurable_const

theorem dens_meas (hW : Measurable W) :
    Measurable fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal :=
  (hW.comp measurable_cpt).ennreal_toReal.ennreal_ofReal

theorem nuF_ac : nuF X x0 W FF ≪ muF X x0 := by
  unfold nuF
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private lemma measurableSet_dom' : MeasurableSet X.dom := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hd : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
    Continuous.matrix_det (A := fun x : Frame X.Ψ r => mat x τ) (continuous_apply τ)
  have ho : IsOpen X.dom := by
    show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hd τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  exact ho.measurableSet

theorem memLp_of (hW : Measurable W) {h : Frame X.Ψ r → ℂ} (hh : ContinuousOn h X.dom)
    (hF : InFF X x0 W FF h) : MemLp (fun z => h (cpt X x0 z)) 2 (nuF X x0 W FF) := by
  classical
  unfold InFF at hF
  have hOm : MeasurableSet (OmF X x0) := measurable_cpt measurableSet_dom'
  have hae : ∀ᵐ z ∂nuF X x0 W FF, z ∈ OmF X x0 := by
    have h1 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
      unfold muF
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
    exact nuF_ac.ae_le h1
  have hg : Measurable (X.dom.piecewise h 0) :=
    ContinuousOn.measurable_piecewise hh continuous_const.continuousOn measurableSet_dom'
  have hm : AEStronglyMeasurable (fun z => h (cpt X x0 z)) (nuF X x0 W FF) := by
    have hm0 : Measurable fun z => X.dom.piecewise h 0 (cpt X x0 z) := hg.comp measurable_cpt
    refine hm0.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z hz
    exact Set.piecewise_eq_of_mem _ _ _ hz
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by
    simp only [Pi.zero_apply]
    positivity)]
  refine lt_of_le_of_lt ?_ hF
  unfold nuF
  refine (lintegral_withDensity_le_lintegral_mul _ (dens_meas hW) _).trans (lintegral_mono fun z => ?_)
  simp only [Pi.mul_apply]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le

theorem integral_nu (hW : Measurable W) (g : V (nd X) → ℂ) :
    ∫ z, g z ∂nuF X x0 W FF = ∫ z in FF, g z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  unfold nuF
  rw [integral_withDensity_eq_integral_toReal_smul (dens_meas hW)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, Complex.real_smul, mul_comm]

theorem inner_toLp (hW : Measurable W) {a b : V (nd X) → ℂ} (ha : MemLp a 2 (nuF X x0 W FF))
    (hb : MemLp b 2 (nuF X x0 W FF)) :
    ⟪ha.toLp a, hb.toLp b⟫_ℂ = ∫ z in FF, conj (a z) * b z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ z ∂nuF X x0 W FF, ⟪(ha.toLp a) z, (hb.toLp b) z⟫_ℂ = conj (a z) * b z := by
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply] <;> ring
  rw [integral_congr_ae h, integral_nu hW]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI

import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix

noncomputable section

variable {n : ℕ}

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.mpr le_top
  | simp
  | decide
  | exact le_top

theorem levi_logNormSq_zero_at (g : V n → ℂ) (v0 : V n) (hg : ContDiffAt ℂ 2 g v0)
    (hne : g v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hev1 : ∀ᶠ y in 𝓝 v0, ContDiffAt ℂ 2 g y := hg.eventually (by norm_num)
  have hev2 : ∀ᶠ y in 𝓝 v0, g y ≠ 0 := hg.continuousAt.eventually_ne hne
  have hwdb : ∀ k, wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y) := by
    intro k
    filter_upwards [hev1, hev2] with y hy1 hy2
    have hdg : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y :=
      ((hy1.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
    have hre : HasFDerivAt (fun w => (g w).re)
        (Complex.reCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.reCLM.hasFDerivAt.comp y hdg
    have him : HasFDerivAt (fun w => (g w).im)
        (Complex.imCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.imCLM.hasFDerivAt.comp y hdg
    have hN := (hre.mul hre).add (him.mul him)
    have hpos : 0 < (g y).re * (g y).re + (g y).im * (g y).im := by
      rw [← Complex.normSq_apply]
      exact Complex.normSq_pos.mpr hy2
    have hh := (Complex.ofRealCLM.hasFDerivAt.comp y (hN.log hpos.ne')).congr_of_eventuallyEq
      (f₁ := fun w => ((Real.log (Complex.normSq (g w)) : ℝ) : ℂ))
      (Filter.Eventually.of_forall fun w => by simp [Complex.normSq_apply])
    simp only [wdb]
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_restrictScalars',
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul, map_smul]
    have hz0 : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := hpos.ne'
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
      field_simp <;>
      ring
  have hgd : DifferentiableAt ℂ g v0 := hg.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℂ (fderiv ℂ g) v0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hwd : ∀ j k, wd n j (wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ))) v0 = 0 := by
    intro j k
    have hφ : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0 := by
      have hm := (hD.clm_apply (differentiableAt_const (bas n k))).mul (hgd.inv hne)
      simp only [div_eq_mul_inv]
      exact hm
    have hc : HasFDerivAt (fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          ((fderiv ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0).restrictScalars ℝ)) v0 :=
      (Complex.conjCLE.hasFDerivAt.comp v0 (hφ.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by simp)
    simp only [wd]
    rw [(hwdb k).fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
      Complex.conj_I]
    simp [← mul_assoc, Complex.I_mul_I]
  unfold leviV
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [hwd j k]
  ring

theorem normSq_contDiffAt {g : V n → ℂ} {x : V n} {k : WithTop ℕ∞} (hg : ContDiffAt ℂ k g x) :
    ContDiffAt ℝ k (fun y => Complex.normSq (g y)) x := by
  have h := ContDiffAt.norm_sq ℂ (hg.restrict_scalars ℝ)
  convert h using 1
  funext y
  exact Complex.normSq_eq_norm_sq _

def epunct (e : V n → ℝ) (g : V n → ℂ) (y : V n) : ℝ :=
  e y + (Real.log (1 + Complex.normSq (g y)) - Real.log (Complex.normSq (g y)))

variable {U : Set (V n)}

theorem isOpen_punct (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    IsOpen {y | y ∈ U ∧ g y ≠ 0} := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton

theorem contDiffAt_of_punct (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℂ ∞ g y := (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hy)

theorem epunct_parts (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) {y : V n} (hy : y ∈ U) (hgy : g y ≠ 0) :
    ContDiffAt ℝ ∞ e y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (1 + Complex.normSq (g w))) y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (Complex.normSq (g w))) y := by
  have hN := normSq_contDiffAt (contDiffAt_of_punct hU hg hy)
  refine ⟨he.contDiffAt (hU.mem_nhds hy), ?_, ?_⟩
  · refine (contDiffAt_const.add hN).log ?_
    have h0 := Complex.normSq_nonneg (g y)
    have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
    exact h1.ne'
  · exact hN.log (Complex.normSq_pos.mpr hgy).ne'

theorem epunct_smooth (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ (epunct e g) {y | y ∈ U ∧ g y ≠ 0} := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := epunct_parts hU he hg hy.1 hy.2
  exact (h1.add (h2.sub h3)).contDiffWithinAt

theorem epunct_levi (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    ∀ y ∈ {y | y ∈ U ∧ g y ≠ 0}, ∀ ξ : Fin n → ℂ,
      0 ≤ (leviV n (fun w => (epunct e g w : ℂ)) y ξ).re := by
  intro y hy ξ
  have hU' := isOpen_punct hU hg
  obtain ⟨h1, h2, h3⟩ := epunct_parts hU he hg hy.1 hy.2
  have h12 := h1.of_le two_le_inf
  have h22 := h2.of_le two_le_inf
  have h32 := h3.of_le two_le_inf
  have hsplit : leviV n (fun w => (epunct e g w : ℂ)) y ξ =
      leviV n (fun w => (e w : ℂ)) y ξ +
        (leviV n (fun w => (Real.log (1 + Complex.normSq (g w)) : ℂ)) y ξ +
          (-1 : ℝ) * leviV n (fun w => (Real.log (Complex.normSq (g w)) : ℂ)) y ξ) := by
    have e1 : (fun w => (epunct e g w : ℂ)) = fun w => ((e w +
        (Real.log (1 + Complex.normSq (g w)) + (-1) * Real.log (Complex.normSq (g w))) : ℝ) : ℂ) := by
      funext w; simp only [epunct]; push_cast; ring
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h12 (h22.add (contDiffAt_const.mul h32)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h22 (contDiffAt_const.mul h32),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) h32]
  rw [hsplit, levi_logNormSq_zero_at g y ((contDiffAt_of_punct hU hg hy.1).of_le two_le_inf) hy.2 ξ]
  have hlse := lseV n 2 _ (fun i : Fin 2 => ![fun _ => Complex.normSq (1 : ℂ), fun w => Complex.normSq (g w)] i) hU'
    (fun i => Or.inr (by
      fin_cases i
      · exact ⟨fun _ => 1, contDiffOn_const, fun _ _ => rfl⟩
      · exact ⟨g, ((contDiffOn_of_differentiableOn n g U hU hg).of_le two_le_inf).mono
          (fun w hw => hw.1), fun _ _ => rfl⟩))
    (fun w _ => by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one]
      linarith [Complex.normSq_nonneg (g w)]) y hy ξ
  have e2 : (fun w => ((Real.log (∑ i : Fin 2, ![fun _ => Complex.normSq (1 : ℂ),
      fun w => Complex.normSq (g w)] i w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + Complex.normSq (g w)) : ℝ) : ℂ) := by
    funext w; simp [Fin.sum_univ_two]
  rw [e2] at hlse
  simp only [mul_zero, add_zero, Complex.add_re]
  exact add_nonneg (hel y hy.1 ξ) hlse

theorem log_gap_pos {N : ℝ} (hN : 0 < N) : 0 < Real.log (1 + N) - Real.log N := by
  exact sub_pos.mpr (Real.log_lt_log hN (by linarith))

theorem epunct_compact (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U)
    (hec : ∀ a, IsCompact {y | y ∈ U ∧ e y ≤ a}) (he0 : ∀ y ∈ U, 0 ≤ e y)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) (a : ℝ) :
    IsCompact {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} := by
  let K : Set (V n) := {y | y ∈ U ∧ e y ≤ a}
  let K1 : Set (V n) := K ∩ (fun y => Real.exp a * Complex.normSq (g y)) ⁻¹' Set.Ici 1
  let K2 : Set (V n) := K1 ∩ (epunct e g) ⁻¹' Set.Iic a
  have hK : IsCompact K := hec a
  have hc1 : ContinuousOn (fun y => Real.exp a * Complex.normSq (g y)) K :=
    continuousOn_const.mul
      (Complex.continuous_normSq.comp_continuousOn (hg.continuousOn.mono fun y hy => hy.1))
  have hK1 : IsClosed K1 := hc1.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  have hcont : ContinuousOn (epunct e g) K1 := by
    intro y hy
    have hyU : y ∈ U := hy.1.1
    have hN : Complex.normSq (g y) ≠ 0 := by
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy.2
      rw [h0, mul_zero] at h2
      linarith
    have hgc : ContinuousAt g y := (hg.differentiableAt (hU.mem_nhds hyU)).continuousAt
    have hNc : ContinuousAt (fun w => Complex.normSq (g w)) y :=
      Complex.continuous_normSq.continuousAt.comp hgc
    have hec' : ContinuousAt e y := (he.contDiffAt (hU.mem_nhds hyU)).continuousAt
    have h1 : (1 : ℝ) + Complex.normSq (g y) ≠ 0 := by
      have h0 := Complex.normSq_nonneg (g y)
      have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
      exact h1.ne'
    exact (hec'.add (((continuousAt_const.add hNc).log h1).sub (hNc.log hN))).continuousWithinAt
  have hK2 : IsClosed K2 := hcont.preimage_isClosed_of_isClosed hK1 isClosed_Iic
  have heq : {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} = K2 := by
    ext y
    constructor
    · rintro ⟨⟨hyU, hgy⟩, hya⟩
      have hNpos : 0 < Complex.normSq (g y) := Complex.normSq_pos.mpr hgy
      have hgap := log_gap_pos hNpos
      have he0y := he0 y hyU
      have hdef : epunct e g y = e y + (Real.log (1 + Complex.normSq (g y)) -
          Real.log (Complex.normSq (g y))) := rfl
      have hya' : epunct e g y ≤ a := hya
      refine ⟨⟨⟨hyU, by linarith⟩, ?_⟩, hya⟩
      show 1 ≤ Real.exp a * Complex.normSq (g y)
      have h1 : Real.log (1 + Complex.normSq (g y)) ≤ a + Real.log (Complex.normSq (g y)) := by
        linarith
      rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, Real.exp_log hNpos] at h1
      linarith
    · rintro ⟨⟨⟨hyU, -⟩, hy1⟩, hya⟩
      refine ⟨⟨hyU, ?_⟩, hya⟩
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy1
      rw [h0, Complex.normSq_zero, mul_zero] at h2
      linarith
  rw [heq]
  exact hK.of_isClosed_subset hK2 (fun y hy => hy.1.1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE

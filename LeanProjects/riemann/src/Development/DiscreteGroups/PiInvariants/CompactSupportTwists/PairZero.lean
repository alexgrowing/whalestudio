import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TsumEnormEq

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace DiscreteGroups.T1.G

variable (X : Ctx)

theorem pair_zero (hr : X.μ.IsMulRightInvariant) (hb : KerBasic) (hl2 : KernelL2RowsColumns) {φ : X.G → ℂ} (hφ : Tst φ)
    {f : X.G → ℂ} (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν)
    {h : X.G → ℂ} (hh : MemLp h 2 X.ν)
    (hz : ∀ z, ∫ x, starRingEnd ℂ (h x) * f (x * z) ∂X.ν = 0) :
    Integrable (fun x => starRingEnd ℂ (h x) * ∫ y, ker X.Γ φ x y * f y ∂X.ν) X.ν ∧
    ∫ x, starRingEnd ℂ (h x) * ∫ y, ker X.Γ φ x y * f y ∂X.ν ∂X.ν = 0 := by
  haveI := hr
  haveI : SigmaFinite X.ν := by unfold Ctx.ν; infer_instance
  have hfm : AEStronglyMeasurable f X.μ := aesm_of_inv X hinv hf.1
  have hνμ : X.ν ≪ X.μ := Measure.absolutelyContinuous_of_le (Measure.restrict_le_self : X.μ.restrict X.F ≤ X.μ)
  have hin : ∀ x, ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := fun x => by
    rw [(unfold X hb hl2 hφ hinv hf x).2, ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
    simp
  simp only [hin]
  set Fc : X.G → X.G → ℂ := fun x z => starRingEnd ℂ (h x) * (φ z * f (x * z)) with hFc
  have hFm : AEStronglyMeasurable (Function.uncurry Fc) (X.ν.prod X.μ) := by
    have h1 : AEStronglyMeasurable (fun p : X.G × X.G => starRingEnd ℂ (h p.1)) (X.ν.prod X.μ) :=
      Complex.continuous_conj.comp_aestronglyMeasurable hh.1.comp_fst
    have h2 : AEStronglyMeasurable (fun p : X.G × X.G => φ p.2) (X.ν.prod X.μ) :=
      (hφ.1.comp continuous_snd).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : X.G × X.G => f (p.1 * p.2)) (X.ν.prod X.μ) := by
      have := (hfm.comp_snd (μ := X.μ)).comp_measurePreserving (measurePreserving_prod_mul X.μ X.μ)
      exact this.mono_ac (hνμ.prod Measure.AbsolutelyContinuous.rfl)
    exact h1.mul (h2.mul h3)
  have eh : eLpNorm h 2 X.ν = (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂X.ν) ^ (1 / (2:ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  have ef : eLpNorm f 2 X.ν = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂X.ν) ^ (1 / (2:ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  have hz_bd : ∀ z, ∫⁻ x, ‖Fc x z‖ₑ ∂X.ν ≤ ‖φ z‖ₑ * (eLpNorm h 2 X.ν * eLpNorm f 2 X.ν) := fun z => by
    have e : ∀ x, ‖Fc x z‖ₑ = ‖φ z‖ₑ * (‖h x‖ₑ * ‖f (x * z)‖ₑ) := fun x => by
      simp only [hFc, enorm_mul, enorm_conj']
      ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    gcongr
    have hfz : AEStronglyMeasurable (fun x => f (x * z)) X.ν :=
      (hfm.comp_measurePreserving (measurePreserving_mul_right X.μ z)).mono_ac hνμ
    have hol := ENNReal.lintegral_mul_le_Lp_mul_Lq X.ν Real.HolderConjugate.two_two hh.1.enorm hfz.enorm
    have hrt := lint_rt X hr (g := fun y => ‖f y‖ₑ ^ (2:ℝ)) (fun γ y => by simp only [hinv γ y]) z
    simp only [Pi.mul_apply] at hol
    rw [hrt] at hol
    rw [eh, ef]
    exact hol
  have hφint : ∫⁻ z, ‖φ z‖ₑ ∂X.μ < ⊤ := (hφ.1.integrable_of_hasCompactSupport hφ.2).2
  have hfin : ∫⁻ p, ‖Function.uncurry Fc p‖ₑ ∂(X.ν.prod X.μ) < ⊤ := by
    rw [lintegral_prod_symm _ hFm.enorm]
    calc ∫⁻ z, ∫⁻ x, ‖Function.uncurry Fc (x, z)‖ₑ ∂X.ν ∂X.μ
        ≤ ∫⁻ z, ‖φ z‖ₑ * (eLpNorm h 2 X.ν * eLpNorm f 2 X.ν) ∂X.μ := lintegral_mono fun z => hz_bd z
      _ = (∫⁻ z, ‖φ z‖ₑ ∂X.μ) * (eLpNorm h 2 X.ν * eLpNorm f 2 X.ν) :=
        lintegral_mul_const' _ _ (ENNReal.mul_ne_top hh.eLpNorm_lt_top.ne hf.eLpNorm_lt_top.ne)
      _ < ⊤ := ENNReal.mul_lt_top hφint (ENNReal.mul_lt_top hh.eLpNorm_lt_top hf.eLpNorm_lt_top)
  have hFi : Integrable (Function.uncurry Fc) (X.ν.prod X.μ) := ⟨hFm, hfin⟩
  refine ⟨?_, ?_⟩
  · refine hFi.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFc, Function.uncurry_apply_pair]
    exact integral_const_mul _ _
  · calc ∫ x, starRingEnd ℂ (h x) * ∫ z, φ z * f (x * z) ∂X.μ ∂X.ν = ∫ x, ∫ z, Fc x z ∂X.μ ∂X.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hFc]
          exact (integral_const_mul _ _).symm
      _ = ∫ z, ∫ x, Fc x z ∂X.ν ∂X.μ := integral_integral_swap hFi
      _ = ∫ z, φ z * ∫ x, starRingEnd ℂ (h x) * f (x * z) ∂X.ν ∂X.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [hFc]
          rw [← integral_const_mul]
          congr 1
          funext x
          ring
      _ = 0 := by simp [hz]

end DiscreteGroups.T1.G

end

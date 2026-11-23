import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Schur

theorem lintegral_weighted_sq_le {α : Type} [MeasurableSpace α] (ν : Measure α)
    (u g : α → ℝ≥0∞) (hu : Measurable u) (hg : Measurable g) :
    (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ (∫⁻ y, u y ∂ν) * ∫⁻ y, u y * g y ^ 2 ∂ν := by
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs : Measurable fun y => u y ^ (1 / 2 : ℝ) := hu.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hs.aemeasurable
    (hs.mul hg).aemeasurable
  have e1 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * ((fun y => u y ^ (1 / 2 : ℝ)) * g)) a ∂ν
      = ∫⁻ y, u y * g y ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← sq, hsq]
  have e2 : ∫⁻ a, (u a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ν = ∫⁻ y, u y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.rpow_two, hsq]
  have e3 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * g) a ^ (2 : ℝ) ∂ν = ∫⁻ y, u y * g y ^ 2 ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.rpow_two, mul_pow, hsq]
  rw [e1, e2, e3] at h
  calc (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ _ := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, hsq, hsq]

theorem schurL : SchurL := by
  intro α _ ν _ k A f hk hf hrow hcol
  have hk1 : ∀ x, Measurable (k x) := fun x => hk.of_uncurry_left
  have hk2 : ∀ y, Measurable fun x => k x y := fun y => hk.of_uncurry_right
  have hgm : Measurable (hf.mk f) := hf.measurable_mk
  set g := hf.mk f with hgdef
  have hfg : f =ᵐ[ν] g := hf.ae_eq_mk
  have e1 : ∀ x, ∫⁻ y, k x y * f y ∂ν = ∫⁻ y, k x y * g y ∂ν := fun x =>
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have e2 : ∫⁻ y, f y ^ 2 ∂ν = ∫⁻ y, g y ^ 2 ∂ν :=
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have hF : Measurable (Function.uncurry fun x y => k x y * g y ^ 2) :=
    hk.mul ((hgm.pow_const 2).comp measurable_snd)
  have hQ : Measurable fun x => ∫⁻ y, k x y * g y ^ 2 ∂ν := hF.lintegral_prod_right'
  simp only [e1, e2]
  calc ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, A * ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := by
        refine lintegral_mono fun x => ?_
        exact (lintegral_weighted_sq_le ν (k x) g (hk1 x) hgm).trans (by gcongr; exact hrow x)
    _ = A * ∫⁻ x, ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := lintegral_const_mul _ hQ
    _ = A * ∫⁻ y, ∫⁻ x, k x y * g y ^ 2 ∂ν ∂ν := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = A * ∫⁻ y, (∫⁻ x, k x y ∂ν) * g y ^ 2 ∂ν := by
        congr 1
        exact lintegral_congr fun y => lintegral_mul_const _ (hk2 y)
    _ ≤ A * ∫⁻ y, A * g y ^ 2 ∂ν := by
        gcongr with y
        exact hcol y
    _ = A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hgm.pow_const 2), sq, mul_assoc]

end GlobalTheory.CompanionTheory.Schur

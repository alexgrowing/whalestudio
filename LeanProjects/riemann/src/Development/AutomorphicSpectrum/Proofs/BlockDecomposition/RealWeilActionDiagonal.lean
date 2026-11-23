import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasTemperateGrowthConjPow
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.RealSim

theorem integral_mul_left_volC {z : ℂ} (hz : z ≠ 0) (F : ℂ → ℂ) :
    ∫ v, F v ∂volC = ((Complex.normSq z : ℝ) : ℂ) * ∫ u, F (z * u) ∂volC := by
  have hN : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ z) = Complex.normSq z := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hmap : Measure.map (fun u : ℂ => z * u) (volume : Measure ℂ) =
      ENNReal.ofReal |(Complex.normSq z)⁻¹| • volume := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
      (f := LinearMap.mulLeft ℝ z) (by rw [hdet]; exact hN.ne')
    rw [hdet] at h
    exact h
  have hemb : MeasurableEmbedding (fun u : ℂ => z * u) :=
    (Homeomorph.mulLeft₀ z hz).measurableEmbedding
  have h1 : ∫ u, F (z * u) ∂(volume : Measure ℂ) =
      ((Complex.normSq z : ℝ) : ℂ)⁻¹ * ∫ v, F v ∂(volume : Measure ℂ) := by
    rw [← hemb.integral_map (g := F) (μ := volume), hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hN), Complex.real_smul]
    push_cast
    rfl
  have hN' : ((Complex.normSq z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold volC
  rw [integral_smul_measure, integral_smul_measure, h1]
  simp only [Complex.real_smul, ENNReal.toReal_ofNat, smul_eq_mul]
  field_simp

theorem rWR_sim (n : ℤ) {z : ℂ} (hz : z ≠ 0) {r a : ℝ} (hr : r = ‖z‖) (ha : a = r ^ 2)
    (A B C d s : ℝ) (x : ℂ) :
    rWR A (a * B) (C / a) d (fun y => PhiInf n (y * ((r * s : ℝ) : ℂ))) x =
      (z / (r : ℂ)) ^ n * rWR A B C d (fun y => PhiInf n (y * (s : ℂ))) (x * z) := by
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hz
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hapos : 0 < a := by rw [ha]; positivity
  set w : ℂ := z / (r : ℂ) with hwdef
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, ← hr]
    exact div_self hrpos.ne'
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  have hzw : z = (r : ℂ) * w := by rw [hwdef]; field_simp
  have hNz : Complex.normSq z = a := by rw [Complex.normSq_eq_norm_sq, ← hr, ha]
  have hNm : ∀ y : ℂ, Complex.normSq (y * z) = a * Complex.normSq y := by
    intro y; rw [map_mul, hNz]; ring
  have hwn : w ^ n * w ^ (-n) = 1 := by
    rw [← zpow_add₀ hw0]; simp
  have hP : ∀ y : ℂ, PhiInf n (y * w) = w ^ (-n) * PhiInf n y :=
    fun y => (GlobalTheory.CompanionTheory.PhiInfIso.phiIso n).2 y w hw1
  by_cases hC : C = 0
  · subst hC
    have e1 : A * (a * B) * Complex.normSq x = A * B * Complex.normSq (x * z) := by
      rw [hNm]; ring
    have e2 : (A : ℂ) * (x * z) * (s : ℂ) = (A : ℂ) * x * ((r * s : ℝ) : ℂ) * w := by
      rw [hzw]; push_cast; ring
    simp only [rWR, zero_div, if_true]
    rw [e1, e2, hP]
    linear_combination (Complex.exp (2 * Real.pi * Complex.I * ((A * B * Complex.normSq (x * z) : ℝ) : ℂ)) *
      sgR A * ((|A| : ℝ) : ℂ) * PhiInf n ((A : ℂ) * x * ((r * s : ℝ) : ℂ))) * (-hwn)
  · have hCa : C / a ≠ 0 := div_ne_zero hC hapos.ne'
    have hsg : sgR (-(C / a)) = sgR (-C) := by
      unfold sgR
      have : 0 < -(C / a) ↔ 0 < -C := by
        rw [← neg_div, div_pos_iff_of_pos_right hapos]
      simp only [this]
    have habs : |C / a|⁻¹ = a * |C|⁻¹ := by
      rw [abs_div, abs_of_pos hapos]
      field_simp
    have hre : ∀ u : ℂ, ((starRingEnd ℂ) (x * z) * (z * u)).re = a * ((starRingEnd ℂ) x * u).re := by
      intro u
      have : (starRingEnd ℂ) (x * z) * (z * u) = (a : ℂ) * ((starRingEnd ℂ) x * u) := by
        rw [map_mul, ← hNz, Complex.normSq_eq_conj_mul_self]
        ring
      rw [this, Complex.re_ofReal_mul]
    have hint : ∀ u : ℂ,
        Complex.exp (2 * Real.pi * Complex.I *
          (((A * Complex.normSq (x * z) + d * Complex.normSq (z * u) -
            2 * ((starRingEnd ℂ) (x * z) * (z * u)).re) / C : ℝ) : ℂ)) *
          PhiInf n (z * u * (s : ℂ)) =
        w ^ (-n) * (Complex.exp (2 * Real.pi * Complex.I *
          (((A * Complex.normSq x + d * Complex.normSq u -
            2 * ((starRingEnd ℂ) x * u).re) / (C / a) : ℝ) : ℂ)) *
          PhiInf n (u * ((r * s : ℝ) : ℂ))) := by
      intro u
      have e1 : (A * Complex.normSq (x * z) + d * Complex.normSq (z * u) -
            2 * ((starRingEnd ℂ) (x * z) * (z * u)).re) / C =
          (A * Complex.normSq x + d * Complex.normSq u -
            2 * ((starRingEnd ℂ) x * u).re) / (C / a) := by
        rw [hNm, mul_comm z u, hNm, mul_comm u z, hre]
        field_simp
      have e2 : z * u * (s : ℂ) = u * ((r * s : ℝ) : ℂ) * w := by
        rw [hzw]; push_cast; ring
      rw [e1, e2, hP]
      ring
    simp only [rWR, if_neg hC, if_neg hCa]
    have hJ := integral_mul_left_volC hz (fun v : ℂ => Complex.exp (2 * Real.pi * Complex.I *
      (((A * Complex.normSq (x * z) + d * Complex.normSq v -
        2 * ((starRingEnd ℂ) (x * z) * v).re) / C : ℝ) : ℂ)) * PhiInf n (v * (s : ℂ)))
    simp only [hint] at hJ
    rw [hJ, integral_const_mul, hsg, habs, hNz]
    have key : ∀ J : ℂ, Complex.I * sgR (-C) * ((a * |C|⁻¹ : ℝ) : ℂ) * J =
        w ^ n * (Complex.I * sgR (-C) * ((|C|⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (w ^ (-n) * J))) := by
      intro J
      rw [Complex.ofReal_mul]
      linear_combination (-(Complex.I * sgR (-C) * (a : ℂ) * ((|C|⁻¹ : ℝ) : ℂ) * J)) * hwn
    exact key _

theorem piRc_sim : ∀ (n : ℤ) (t : ℝ) (z : ℂˣ) (a : ℝˣ), (a : ℝ) = ‖(z : ℂ)‖ ^ 2 → ∀ (g : GL (Fin 2) ℝ) (x : ℂ),
    piRc (chC n (Complex.I * t)) (dg2 a 1 * g) (PhiInf n) x =
      chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * piRc (chC n (Complex.I * t)) g (PhiInf n) (x * z) := by
  intro n t z a ha g x
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  set r : ℝ := ‖(z : ℂ)‖ with hrdef
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hapos : 0 < (a : ℝ) := by rw [ha]; positivity
  have hdet : ((dg2 a 1 * g).val).det = (a : ℝ) * (g.val).det := by
    show ((dg2 a 1).val * g.val).det = _
    rw [Matrix.det_mul]
    congr 1
    simp [dg2, Matrix.det_fin_two]
  by_cases h : 0 < (g.val).det
  swap
  · have h' : ¬ 0 < ((dg2 a 1 * g).val).det := by
      rw [hdet]
      intro h2
      exact h ((mul_pos_iff_of_pos_left hapos).mp h2)
    unfold piRc
    rw [dif_neg h, dif_neg h', mul_zero]
  have h' : 0 < ((dg2 a 1 * g).val).det := by rw [hdet]; exact mul_pos hapos h
  unfold piRc
  rw [dif_pos h, dif_pos h']
  set D : ℝ := (g.val).det with hD
  have hs : Real.sqrt ((dg2 a 1 * g).val).det = r * Real.sqrt D := by
    rw [hdet, ha, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
  have hpm : 0 < Real.sqrt D := Real.sqrt_pos.mpr h
  have e00 : (dg2 a 1 * g).val 0 0 = (a : ℝ) * g.val 0 0 := by
    show ((dg2 a 1).val * g.val) 0 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 a 1 * g).val 0 1 = (a : ℝ) * g.val 0 1 := by
    show ((dg2 a 1).val * g.val) 0 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 a 1 * g).val 1 0 = g.val 1 0 := by
    show ((dg2 a 1).val * g.val) 1 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 a 1 * g).val 1 1 = g.val 1 1 := by
    show ((dg2 a 1).val * g.val) 1 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hchi := GlobalTheory.CompanionTheory.CenTheta.RealCentral.chC_pos_mul n (Complex.I * t) hr hpm
    (Units.mk0 ((r : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne'))
    (Units.mk0 ((Real.sqrt D : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hpm.ne'))
    (Units.mk0 ((Real.sqrt ((dg2 a 1 * g).val).det : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h').ne')) rfl rfl (by simp only [Units.val_mk0, hs])
  have hchz : chC n (Complex.I * t) z = ((z : ℂ) / (r : ℂ)) ^ n *
      chC n (Complex.I * t) (Units.mk0 ((r : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')) := by
    have hn : ‖((Units.mk0 ((r : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') : ℂˣ) : ℂ)‖ = r := by
      rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    unfold chC
    rw [hn, Units.val_mk0, div_self hrC, one_zpow, one_mul]
  rw [hchi]
  have q00 : (dg2 a 1 * g).val 0 0 / ((dg2 a 1 * g).val).det = g.val 0 0 / D := by
    rw [e00, hdet]
    have : D ≠ 0 := h.ne'
    field_simp
  have q10 : (dg2 a 1 * g).val 1 0 / ((dg2 a 1 * g).val).det = g.val 1 0 / D / (a : ℝ) := by
    rw [e10, hdet]
    have : D ≠ 0 := h.ne'
    field_simp
  rw [q00, q10, e01, e11, hs, rWR_sim n hz rfl ha, hchz]
  push_cast
  ring

end GlobalTheory.CompanionTheory.FexTheta.RealSim

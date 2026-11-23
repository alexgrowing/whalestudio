import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasTemperateGrowthConjPow
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta.RealCentral

theorem rWR_const_mul (a b c d : ℝ) (k : ℂ) (F : ℂ → ℂ) (x : ℂ) :
    rWR a b c d (fun z => k * F z) x = k * rWR a b c d F x := by
  unfold rWR
  split_ifs with hc
  · ring
  · have e : ∀ u : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq x + d * Complex.normSq u - 2 * ((starRingEnd ℂ) x * u).re) / c : ℝ) : ℂ)) * (k * F u)
        = k * (Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq x + d * Complex.normSq u - 2 * ((starRingEnd ℂ) x * u).re) / c : ℝ) : ℂ)) * F u) := by
      intro u; ring
    simp_rw [e]
    rw [integral_const_mul]
    ring

theorem chC_pos_mul (n : ℤ) (s : ℂ) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (u v w : ℂˣ)
    (hu : (u : ℂ) = (r : ℂ)) (hv : (v : ℂ) = (q : ℂ)) (hw : (w : ℂ) = ((r * q : ℝ) : ℂ)) :
    chC n s w = chC n s u * chC n s v := by
  have key : ∀ (p : ℝ), 0 < p → ∀ y : ℂˣ, (y : ℂ) = (p : ℂ) →
      chC n s y = (((p ^ 2 : ℝ)) : ℂ) ^ s := by
    intro p hp y hy
    unfold chC
    have h1 : ‖(y : ℂ)‖ = p := by rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    have h2 : (y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ) = 1 := by
      rw [h1, hy]; exact div_self (by exact_mod_cast hp.ne')
    rw [h2, one_zpow, one_mul, h1]
  rw [key _ (mul_pos hr hq) w hw, key r hr u hu, key q hq v hv, mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg r) (sq_nonneg q)]

theorem sgR_norm (a : ℝ) : ‖sgR a‖ = 1 := by
  unfold sgR; split_ifs <;> simp

theorem sgR_zpow (n : ℤ) (a : ℝ) : sgR a ^ (-n) = (if 0 < a then 1 else (-1 : ℂ) ^ n) := by
  unfold sgR
  split_ifs
  · simp
  · rw [zpow_neg, ← inv_zpow]; norm_num

theorem abs_mul_inv {a : ℝ} (ha : a ≠ 0) : (((|a| : ℝ) : ℂ)) * ((a⁻¹ : ℝ) : ℂ) = sgR a := by
  unfold sgR
  split_ifs with h
  · rw [abs_of_pos h, ← Complex.ofReal_mul, mul_inv_cancel₀ ha]; simp
  · rw [abs_of_nonpos (not_lt.mp h), ← Complex.ofReal_mul, neg_mul, mul_inv_cancel₀ ha]; simp

theorem rWR_diag (n : ℤ) {a : ℝ} (ha : a ≠ 0) (m : ℝ) (z : ℂ) :
    rWR a⁻¹ 0 0 (a⁻¹)⁻¹ (fun y => PhiInf n (y * (((|a| * m : ℝ)) : ℂ))) z =
      (((a⁻¹ : ℝ) : ℂ) * sgR a ^ (-n)) * PhiInf n (z * (m : ℂ)) := by
  rw [GlobalTheory.CompanionTheory.RealWeil.rWR_m (inv_ne_zero ha)]
  have e : ((a⁻¹ : ℝ) : ℂ) * z * (((|a| * m : ℝ)) : ℂ) = z * (m : ℂ) * sgR a := by
    rw [← abs_mul_inv ha]; push_cast; ring
  rw [e, (GlobalTheory.CompanionTheory.PhiInfIso.phiIso n).2 _ _ (sgR_norm a)]
  ring

theorem rWR_central (n : ℤ) {a : ℝ} (ha : a ≠ 0) (g00 g01 g10 g11 : ℝ) {D : ℝ} (hD : 0 < D)
    (hdet : g00 * g11 - g01 * g10 = D) (m : ℝ) (hm : m ≠ 0) (x : ℂ) :
    rWR (g00 / D * a⁻¹) (g01 * a) (g10 / D * a⁻¹) (g11 * a)
        (fun y => PhiInf n (y * (((|a| * m : ℝ)) : ℂ))) x =
      (((a⁻¹ : ℝ) : ℂ) * sgR a ^ (-n)) *
        rWR (g00 / D) g01 (g10 / D) g11 (fun y => PhiInf n (y * (m : ℂ))) x := by
  set g1 : Matrix (Fin 2) (Fin 2) ℝ := !![g00 / D, g01; g10 / D, g11] with hg1
  set mm : Matrix (Fin 2) (Fin 2) ℝ := !![a⁻¹, 0; 0, (a⁻¹)⁻¹] with hmm
  have hd1 : g1.det = 1 := by
    rw [hg1, Matrix.det_fin_two_of]
    field_simp
    linarith
  have hd2 : mm.det = 1 := by
    rw [hmm, Matrix.det_fin_two_of]
    field_simp
    simp
  have hΨ : (fun y => PhiInf n (y * (((|a| * m : ℝ)) : ℂ))) ∈ SchC := by
    have := GlobalTheory.CompanionTheory.RealWeil.dil_mem (s := |a| * m) (mul_ne_zero (abs_ne_zero.mpr ha) hm)
      (GlobalTheory.CompanionTheory.PhiInfIso.phiIso n).1
    simpa only [mul_comm] using this
  have hrep := congrFun (GlobalTheory.CompanionTheory.RealWeil.rwrrep g1 mm hd1 hd2 _ hΨ).2 x
  have h1 : rWRm mm (fun y => PhiInf n (y * (((|a| * m : ℝ)) : ℂ))) =
      fun z => (((a⁻¹ : ℝ) : ℂ) * sgR a ^ (-n)) * (fun y => PhiInf n (y * (m : ℂ))) z := by
    funext z
    exact rWR_diag n ha m z
  rw [h1] at hrep
  have h2 : rWRm g1 (fun z => (((a⁻¹ : ℝ) : ℂ) * sgR a ^ (-n)) * (fun y => PhiInf n (y * (m : ℂ))) z) x =
      (((a⁻¹ : ℝ) : ℂ) * sgR a ^ (-n)) * rWR (g00 / D) g01 (g10 / D) g11 (fun y => PhiInf n (y * (m : ℂ))) x :=
    rWR_const_mul _ _ _ _ _ _ _
  rw [h2] at hrep
  rw [← hrep]
  have e00 : (g1 * mm) 0 0 = g00 / D * a⁻¹ := by simp [hg1, hmm, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g1 * mm) 0 1 = g01 * a := by simp [hg1, hmm, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g1 * mm) 1 0 = g10 / D * a⁻¹ := by simp [hg1, hmm, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g1 * mm) 1 1 = g11 * a := by simp [hg1, hmm, Matrix.mul_apply, Fin.sum_univ_two]
  show _ = rWR ((g1 * mm) 0 0) ((g1 * mm) 0 1) ((g1 * mm) 1 0) ((g1 * mm) 1 1) _ x
  rw [e00, e01, e10, e11]

theorem piRc_central (n : ℤ) (t : ℝ) (a : ℝˣ) (g : GL (Fin 2) ℝ) (x : ℂ) :
    piRc (chC n (Complex.I * t)) (dg2 a a * g) (PhiInf n) x =
      omR n t a * piRc (chC n (Complex.I * t)) g (PhiInf n) x := by
  have ha : (a : ℝ) ≠ 0 := a.ne_zero
  have hdet : ((dg2 a a * g).val).det = (a : ℝ) ^ 2 * (g.val).det := by
    show ((dg2 a a).val * g.val).det = _
    rw [Matrix.det_mul]
    congr 1
    simp [dg2, Matrix.det_fin_two]
    ring
  have ha2 : 0 < (a : ℝ) ^ 2 := by positivity
  by_cases h : 0 < (g.val).det
  swap
  · have h' : ¬ 0 < ((dg2 a a * g).val).det := by
      rw [hdet]
      intro h2
      exact h ((mul_pos_iff_of_pos_left ha2).mp h2)
    unfold piRc
    rw [dif_neg h, dif_neg h', mul_zero]
  have h' : 0 < ((dg2 a a * g).val).det := by rw [hdet]; exact mul_pos ha2 h
  unfold piRc
  rw [dif_pos h, dif_pos h']
  set D : ℝ := (g.val).det with hD
  have hs : Real.sqrt ((dg2 a a * g).val).det = |(a : ℝ)| * Real.sqrt D := by
    rw [hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hpa : 0 < |(a : ℝ)| := abs_pos.mpr ha
  have hpm : 0 < Real.sqrt D := Real.sqrt_pos.mpr h
  have e00 : (dg2 a a * g).val 0 0 = (a : ℝ) * g.val 0 0 := by
    show ((dg2 a a).val * g.val) 0 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 a a * g).val 0 1 = (a : ℝ) * g.val 0 1 := by
    show ((dg2 a a).val * g.val) 0 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 a a * g).val 1 0 = (a : ℝ) * g.val 1 0 := by
    show ((dg2 a a).val * g.val) 1 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 a a * g).val 1 1 = (a : ℝ) * g.val 1 1 := by
    show ((dg2 a a).val * g.val) 1 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hD2 : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = D := by
    rw [hD, Matrix.det_fin_two]
  have hc := rWR_central n ha (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) h hD2
    (Real.sqrt D) hpm.ne' x
  have hchi := chC_pos_mul n (Complex.I * t) hpa hpm
    (Units.mk0 ((|(a : ℝ)| : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha)))
    (Units.mk0 ((Real.sqrt D : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hpm.ne'))
    (Units.mk0 ((Real.sqrt ((dg2 a a * g).val).det : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h').ne')) rfl rfl (by simp only [Units.val_mk0, hs])
  rw [hchi]
  have q00 : (dg2 a a * g).val 0 0 / ((dg2 a a * g).val).det = g.val 0 0 / D * (a : ℝ)⁻¹ := by
    rw [e00, hdet]; field_simp
  have q10 : (dg2 a a * g).val 1 0 / ((dg2 a a * g).val).det = g.val 1 0 / D * (a : ℝ)⁻¹ := by
    rw [e10, hdet]; field_simp
  rw [q00, q10, e01, e11, hs, mul_comm (a : ℝ) (g.val 0 1), mul_comm (a : ℝ) (g.val 1 1), hc]
  unfold omR
  rw [← sgR_zpow, ← abs_mul_inv ha]
  push_cast
  ring

end GlobalTheory.CompanionTheory.CenTheta.RealCentral

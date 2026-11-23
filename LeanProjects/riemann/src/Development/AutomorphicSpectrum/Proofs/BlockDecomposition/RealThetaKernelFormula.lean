import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilThetaRealization
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RealTh.GForm

def pol (n : ℤ) (u : ℂ) : ℂ := if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs

theorem pol_mul (n : ℤ) (x y : ℂ) : pol n (x * y) = pol n x * pol n y := by
  unfold pol
  split_ifs
  · rw [map_mul, mul_pow]
  · rw [mul_pow]

theorem pol_ofReal (n : ℤ) (r : ℝ) : pol n (r : ℂ) = (r : ℂ) ^ n.natAbs := by
  unfold pol
  split_ifs <;> simp

theorem phiInf_eq (n : ℤ) (z : ℂ) :
    PhiInf n z = pol n z * Complex.exp (-2 * Real.pi * ((Complex.normSq z : ℝ) : ℂ)) := rfl

theorem exp_mul_exp_eq_exp_mul_gE (a d c r ρ : ℝ) (hc : c ≠ 0) (v : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I *
        (((a * ρ ^ 2 + d * Complex.normSq v - 2 * (ρ * v.re)) / c : ℝ) : ℂ)) *
      Complex.exp (-2 * Real.pi * ((Complex.normSq (v * r) : ℝ) : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) v := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [gE, ← Complex.exp_add, ← Complex.exp_add, Complex.mul_conj, Complex.add_conj, gA]
  congr 1
  simp only [map_mul, Complex.normSq_ofReal]
  push_cast
  field_simp
  ring

theorem int_rotate (ω : Circle) (F : ℂ → ℂ) : ∫ u, F u = ∫ v, F ((ω : ℂ) * v) := by
  have h := ((rotation ω).measurePreserving).integral_comp
    (rotation ω).toHomeomorph.measurableEmbedding F
  simpa [rotation_apply] using h.symm

theorem int_rot (n : ℤ) (a d c r ρ : ℝ) (hc : c ≠ 0) (ω : Circle) :
    ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq ((ρ : ℂ) * ω) + d * Complex.normSq u -
          2 * (conj ((ρ : ℂ) * ω) * u).re) / c : ℝ) : ℂ)) * PhiInf n (u * r) ∂volC =
    2 * (Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      (r : ℂ) ^ n.natAbs * pol n ω * gJ (gA c d r) (-(2 * Real.pi * ρ) / c) n.natAbs) := by
  have hωω : conj (ω : ℂ) * ω = 1 := by
    rw [mul_comm, Complex.mul_conj, Circle.normSq_coe]
    simp
  have hs : Complex.normSq ((ρ : ℂ) * ω) = ρ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Circle.normSq_coe]
    ring
  have e : ∀ v : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq ((ρ : ℂ) * ω) + d * Complex.normSq (((ω : ℂ) * v)) -
          2 * (conj ((ρ : ℂ) * ω) * ((ω : ℂ) * v)).re) / c : ℝ) : ℂ)) *
        PhiInf n (((ω : ℂ) * v) * r) =
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
        (r : ℂ) ^ n.natAbs * pol n ω *
        (pol n v * gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) v) := by
    intro v
    have h := exp_mul_exp_eq_exp_mul_gE a d c r ρ hc v
    have h1 : Complex.normSq (((ω : ℂ) * v)) = Complex.normSq v := by
      rw [Complex.normSq_mul, Circle.normSq_coe, one_mul]
    have h2 : conj ((ρ : ℂ) * ω) * ((ω : ℂ) * v) = (ρ : ℂ) * v := by
      rw [map_mul, Complex.conj_ofReal]
      linear_combination ((ρ : ℂ) * v) * hωω
    have h3 : ((ρ : ℂ) * v).re = ρ * v.re := by simp
    have h4 : Complex.normSq (((ω : ℂ) * v) * r) = Complex.normSq (v * r) := by
      rw [Complex.normSq_mul, h1, Complex.normSq_mul]
    rw [hs, h1, h2, h3, phiInf_eq, h4, pol_mul, pol_mul, pol_ofReal]
    generalize Complex.exp (2 * Real.pi * Complex.I *
        (((a * ρ ^ 2 + d * Complex.normSq v - 2 * (ρ * v.re)) / c : ℝ) : ℂ)) = E₁ at h ⊢
    generalize Complex.exp (-2 * Real.pi * ((Complex.normSq (v * r) : ℝ) : ℂ)) = E₂ at h ⊢
    linear_combination ((r : ℂ) ^ n.natAbs * pol n ω * pol n v) * h
  rw [volC, integral_smul_measure, int_rotate ω]
  simp only [e]
  rw [integral_const_mul]
  have hint : ∫ u : ℂ, pol n u *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) u =
      gJ (gA c d r) (-(2 * Real.pi * ρ) / c) n.natAbs := by
    unfold pol
    split_ifs
    · rfl
    · exact gJ_conj _ _ _
  rw [hint]
  simp

theorem gform_zero (n : ℤ) (a b c d r : ℝ) (hc : c = 0) (hdet : a * d - b * c = 1) (z : ℂ) :
    rWR a b c d (fun y => PhiInf n (y * r)) z =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        pol n z *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  subst hc
  have had : a * d = 1 := by linarith
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hadC : (a : ℂ) * d = 1 := by exact_mod_cast had
  have hdi : (d : ℂ) = (a : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hadC
  simp only [rWR, if_true, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
  have hsg : sgR a * ((|a| : ℝ) : ℂ) = a := sgR_mul_abs a ha
  rw [mul_assoc (Complex.exp _) (sgR a), hsg]
  have e1 : (d : ℂ) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) = (a : ℂ) ^ (n.natAbs + 1) := by
    rw [hdi, _root_.zpow_neg, _root_.inv_zpow, inv_inv, zpow_natCast]
  rw [e1]
  have hphi : PhiInf n ((a : ℂ) * z * (r : ℂ)) =
      (a : ℂ) ^ n.natAbs * (r : ℂ) ^ n.natAbs * pol n z *
        Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) := by
    have h : Complex.normSq ((a : ℂ) * z * (r : ℂ)) = (a * r) ^ 2 * Complex.normSq z := by
      simp only [Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have h' : (a : ℂ) * z * (r : ℂ) = (a : ℂ) * (r : ℂ) * z := by ring
    rw [phiInf_eq, h, h', pol_mul, pol_mul, pol_ofReal, pol_ofReal]
  rw [hphi]
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (((a * b * Complex.normSq z : ℝ) : ℂ))) *
      Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / d) *
        ((Complex.normSq z : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hdi]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← e2]
  generalize Complex.exp (2 * Real.pi * Complex.I * (((a * b * Complex.normSq z : ℝ) : ℂ))) = E₁
  generalize Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) = E₂
  ring

theorem gform_ne_polar (n : ℤ) (a b c d r ρ : ℝ) (hr : 0 < r) (hc : c ≠ 0)
    (hdet : a * d - b * c = 1) (ω : Circle) :
    rWR a b c d (fun y => PhiInf n (y * r)) ((ρ : ℂ) * ω) =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        ((ρ : ℂ) ^ n.natAbs * pol n ω) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * (ρ : ℂ) ^ 2) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hAre := gA_re c d r hr
  have hA0 : gA c d r ≠ 0 := fun h0 => by simp [h0] at hAre
  set w : ℂ := (d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2) with hw
  have hAw : gA c d r = -(2 * Real.pi * Complex.I * w) / c := by
    rw [gA, hw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [hAw, h0] at hA0
    simp at hA0
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have h1 : (Real.pi : ℂ) / gA c d r = Complex.I * c / (2 * w) := by
    rw [hAw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
  have h2 : Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ) / gA c d r = (ρ : ℂ) / w := by
    rw [hAw]
    push_cast
    field_simp
  have h3 : (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) ^ 2 / gA c d r =
      -(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w) := by
    rw [sq, mul_div_assoc, h2]
    push_cast
    field_simp
  have h4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w) *
        (ρ : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    have e : (a : ℂ) * w - 1 = c * ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) := by
      rw [hw]
      linear_combination hdetC
    have e' : ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w = ((a : ℂ) * w - 1) / (c * w) := by
      rw [e]
      field_simp
    rw [e']
    field_simp
    ring
  have hgJ := gJ_eq (gA c d r) hAre (-(2 * Real.pi * ρ) / c) n.natAbs
  rw [h1, h2, h3] at hgJ
  simp only [rWR, if_neg hc]
  rw [int_rot n a d c r ρ hc ω, hgJ, ← h4, _root_.zpow_neg, zpow_natCast,
    mul_assoc Complex.I (sgR (-c)), sgR_neg_mul c hc]
  generalize Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) = e₁
  generalize Complex.exp (-(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w)) = e₂
  rw [div_pow]
  field_simp
  rw [Complex.I_sq]
  ring

theorem gform (n : ℤ) (a b c d r : ℝ) (hr : 0 < r) (hdet : a * d - b * c = 1) (z : ℂ) :
    rWR a b c d (fun y => PhiInf n (y * r)) z =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        (if 0 ≤ n then (starRingEnd ℂ) z ^ n.natAbs else z ^ n.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  change _ = _ * _ * pol n z * _
  by_cases hc : c = 0
  · exact gform_zero n a b c d r hc hdet z
  · have hz : z = ((‖z‖ : ℝ) : ℂ) * (Circle.exp (Complex.arg z) : ℂ) := by
      rw [Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
    have hs : ((Complex.normSq z : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have hp : pol n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * pol n (Circle.exp (Complex.arg z) : ℂ) := by
      conv_lhs => rw [hz, pol_mul, pol_ofReal]
    rw [hs, hp]
    conv_lhs => rw [hz]
    exact gform_ne_polar n a b c d r ‖z‖ hr hc hdet _

end GlobalTheory.CompanionTheory.RealTh.GForm

import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousOnG2SymmetricInterval
import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open MeasureTheory Set Metric
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume

lemma J_all {u : ℝ} (hu : 0 < u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by
  rcases le_or_gt 1 u with h | h
  · exact J_bound h
  · have hb : ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 1 * |1 - (-1 : ℝ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      rw [norm_mul]
      have h1 : ‖(g0 t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, show g0 t = Real.sqrt (1 - t ^ 2) from rfl,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - t ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
          _ = 1 := Real.sqrt_one
      have h2 : ‖ee u t‖ = 1 := by
        simp only [ee]
        exact Complex.norm_exp_I_mul_ofReal _
      rw [h2, mul_one]
      exact h1
    have hsu : Real.sqrt u ≤ 1 := by
      calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h.le
        _ = 1 := Real.sqrt_one
    have hpos : 0 < u * Real.sqrt u := mul_pos hu (Real.sqrt_pos.mpr hu)
    have hle : u * Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
    have h10 : 2 ≤ 10 / (u * Real.sqrt u) := by
      rw [le_div_iff₀ hpos]
      linarith
    have e2 : (1 : ℝ) * |1 - (-1 : ℝ)| = 2 := by norm_num
    linarith

lemma vol_sq_lt (s : ℝ) : volume {b : ℝ | b ^ 2 < s} = ENNReal.ofReal (2 * Real.sqrt s) := by
  have hset : {b : ℝ | b ^ 2 < s} = Ioo (-Real.sqrt s) (Real.sqrt s) := by
    ext b
    simp only [mem_setOf_eq, mem_Ioo]
    exact Real.sq_lt
  rw [hset, Real.volume_Ioo]
  congr 1
  ring

lemma disc_fubini {R ρ : ℝ} (hR : 0 < R) :
    ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
  classical
  set e := Complex.measurableEquivRealProd with he
  have hpres : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  set F : ℂ → ℂ := (ball (0 : ℂ) R).indicator (fun z => ee ρ z.re) with hF
  set S : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} with hS
  have hmemS : ∀ p : ℝ × ℝ, e.symm p ∈ ball (0 : ℂ) R ↔ p ∈ S := by
    intro p
    rw [Complex.measurableEquivRealProd_symm_apply, mem_ball, dist_zero_right,
      Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_lt' hR]
    rfl
  have hFG : ∀ p : ℝ × ℝ, F (e.symm p) = S.indicator (fun q => ee ρ q.1) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, hF, Set.indicator_of_mem ((hmemS p).mpr hp),
        Complex.measurableEquivRealProd_symm_apply]
    · rw [Set.indicator_of_notMem hp, hF,
        Set.indicator_of_notMem (fun h => hp ((hmemS p).mp h))]
  have hcont : Continuous (fun z : ℂ => ee ρ z.re) := by
    unfold ee
    fun_prop
  have hFint : Integrable F := by
    rw [hF, integrable_indicator_iff measurableSet_ball]
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [ee]
    rw [Complex.norm_exp_I_mul_ofReal]
  have hGint : Integrable (S.indicator (fun q : ℝ × ℝ => ee ρ q.1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    have h1 : (fun p => F (e.symm p)) = S.indicator (fun q : ℝ × ℝ => ee ρ q.1) := funext hFG
    rw [← h1]
    exact (hpres.integrable_comp_emb e.symm.measurableEmbedding).mpr hFint
  have hSmeas : ∀ a : ℝ, MeasurableSet {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} := fun a =>
    measurableSet_lt (by fun_prop) measurable_const
  calc ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ z, F z := (integral_indicator measurableSet_ball).symm
    _ = ∫ p, F (e.symm p) := (hpres.integral_comp' F).symm
    _ = ∫ p, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) p ∂(volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact integral_congr_ae (Filter.Eventually.of_forall hFG)
    _ = ∫ a, ∫ b, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b) := integral_prod _ hGint
    _ = ∫ a, ((2 * Real.sqrt (R ^ 2 - a ^ 2) : ℝ) : ℂ) * ee ρ a := by
        congr 1
        funext a
        have hin : (fun b => S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b)) =
            {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2}.indicator (fun _ => ee ρ a) := by
          funext b
          by_cases hb : b ^ 2 < R ^ 2 - a ^ 2
          · rw [Set.indicator_of_mem (show b ∈ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_mem (show (a, b) ∈ S from show a ^ 2 + b ^ 2 < R ^ 2 by linarith)]
          · rw [Set.indicator_of_notMem (show b ∉ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_notMem (show (a, b) ∉ S from fun h => hb (by
                have h' : a ^ 2 + b ^ 2 < R ^ 2 := h
                linarith))]
        rw [hin, integral_indicator_const _ (hSmeas a), measureReal_def, vol_sq_lt,
          ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    _ = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
        rw [intervalIntegral.integral_of_le (by linarith),
          setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro a ha
        have h2 : R ^ 2 - a ^ 2 ≤ 0 := by
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha
          rcases ha with h | h <;> nlinarith
        rw [Real.sqrt_eq_zero'.mpr h2]
        simp

lemma disc_scale {R ρ : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t =
      ((2 * R ^ 2 : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hsq : ∀ s : ℝ, Real.sqrt (1 - s ^ 2) = Real.sqrt (R ^ 2 - (R * s) ^ 2) / R := by
    intro s
    rw [show R ^ 2 - (R * s) ^ 2 = R ^ 2 * (1 - s ^ 2) by ring, Real.sqrt_mul (sq_nonneg R),
      Real.sqrt_sq hR.le, mul_div_cancel_left₀ _ hR0]
  have hee : ∀ s : ℝ, ee (ρ * R) s = ee ρ (R * s) := by
    intro s
    simp only [ee]
    congr 2
    push_cast
    ring
  have key : (fun s : ℝ => (g0 s : ℂ) * ee (ρ * R) s) =
      fun s => ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    funext s
    rw [hee, show g0 s = Real.sqrt (1 - s ^ 2) from rfl, hsq]
  have hint : (∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s) =
      ∫ s in (-1 : ℝ)..1, ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    rw [key]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => ((Real.sqrt (R ^ 2 - t ^ 2) / R : ℝ) : ℂ) * ee ρ t) hR0
  rw [hint, hcomp, mul_neg, mul_one, Complex.real_smul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  push_cast
  field_simp

end Formalism.FourierDecayAlt.P.DiscFubiniVolume

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem disc_mean_value : C6.DiscMean := by
  intro β hβ
  refine ⟨20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)), fun ξ x₀ R hξ hR => ?_⟩
  classical
  set γ := β * ξ with hγ
  have hγ0 : γ ≠ 0 := mul_ne_zero hβ hξ
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set c : ℝ := ‖γ‖ with hc
  have hpsi : ∀ x : ℂ, G.psi β (ξ * x) = Complex.exp (Complex.I * ((γ * x).re : ℂ)) := by
    intro x
    simp only [G.psi, hγ, mul_assoc]
  have htr : ∫ x in ball x₀ R, G.psi β (ξ * x) =
      Complex.exp (Complex.I * ((γ * x₀).re : ℂ)) *
        ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_const_mul, ← integral_add_left_eq_self _ x₀]
    congr 1
    funext w
    by_cases hw : w ∈ ball (0 : ℂ) R
    · have hw' : x₀ + w ∈ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_mem hw', Set.indicator_of_mem hw, hpsi, mul_add, Complex.add_re,
        Complex.ofReal_add, mul_add, Complex.exp_add]
    · have hw' : x₀ + w ∉ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_notMem hw', Set.indicator_of_notMem hw, mul_zero]
  set u : Circle := Circle.exp (-Complex.arg γ) with hu
  have hrot : ∀ v : ℂ, γ * (rotation u v) = (c : ℂ) * v := by
    intro v
    rw [rotation_apply, hu, Circle.coe_exp]
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I γ]
    calc (↑‖γ‖ * Complex.exp (↑γ.arg * Complex.I)) * (Complex.exp (↑(-γ.arg) * Complex.I) * v)
        = ↑‖γ‖ * (Complex.exp (↑γ.arg * Complex.I) * Complex.exp (↑(-γ.arg) * Complex.I)) * v := by
          ring
      _ = ↑‖γ‖ * v := by
          rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul, add_neg_cancel, Complex.exp_zero,
            mul_one]
  have hrotI : ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) =
      ∫ v in ball (0 : ℂ) R, ee c v.re := by
    have hL := LinearIsometryEquiv.measurePreserving (rotation u)
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← hL.integral_comp (rotation u).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    have hn : rotation u v ∈ ball (0 : ℂ) R ↔ v ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
    by_cases hv : v ∈ ball (0 : ℂ) R
    · rw [Set.indicator_of_mem (hn.mpr hv), Set.indicator_of_mem hv, hrot, Complex.re_ofReal_mul]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hv (hn.mp h)), Set.indicator_of_notMem hv]
  have hvol : (volume (ball x₀ R)).toReal = R ^ 2 * Real.pi := by
    rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
    simp
  have hJ := J_all (u := c * R) (by positivity)
  have hx : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hy : 0 < R * ‖ξ‖ := mul_pos hR (norm_pos_iff.mpr hξ)
  have hcR : c * R = ‖β‖ * (R * ‖ξ‖) := by
    rw [hc, hγ, norm_mul]
    ring
  have hpow : c * R * Real.sqrt (c * R) = (‖β‖ * (R * ‖ξ‖)) ^ (3 / 2 : ℝ) := by
    rw [hcR, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one]
  have hkey : 10 / (c * R * Real.sqrt (c * R)) =
      10 * (‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ))) := by
    rw [hpow, ← Real.mul_rpow hx.le hy.le, Real.rpow_neg (by positivity), div_eq_mul_inv]
  simp only [C6.meanDisc]
  rw [htr, hrotI, disc_fubini hR, disc_scale hR, hvol]
  calc _ = 2 / Real.pi * ‖∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (c * R) s‖ := by
        have hn1 : ‖Complex.exp (Complex.I * ((γ * x₀).re : ℂ))‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        have hn2 : ‖((2 * R ^ 2 : ℝ) : ℂ)‖ = 2 * R ^ 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hn3 : ‖(R ^ 2 * Real.pi)⁻¹‖ = (R ^ 2 * Real.pi)⁻¹ :=
          Real.norm_of_nonneg (by positivity)
        rw [norm_smul, norm_mul, norm_mul, hn1, hn2, hn3]
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        field_simp
    _ ≤ 2 / Real.pi * (10 / (c * R * Real.sqrt (c * R))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ)) := by
        rw [hkey]
        ring

end Formalism.FourierDecayAlt.P

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableBoundedMulWeightFive

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.ParsC

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC.GaussB

def Kf (w : ℂ) : ℝ := (1 + ‖w‖ ^ 2) * Real.exp (-Real.pi * ‖w‖ ^ 2)

lemma poly_mul_gaussian_le_const (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ 3 * ((1 + t ^ 2) * Real.exp (-Real.pi * t ^ 2)) ≤ 216 := by
  have hE : 1 + t ^ 2 / 3 ≤ Real.exp (t ^ 2 / 3) := by
    have := Real.add_one_le_exp (t ^ 2 / 3); linarith
  have h3 : Real.exp (t ^ 2 / 3) ^ 3 = Real.exp (t ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 + t ^ 2 ≤ 3 * Real.exp (t ^ 2 / 3) := by nlinarith [sq_nonneg t]
  have h4 : (1 + t ^ 2) ^ 3 ≤ 27 * Real.exp (t ^ 2) := by
    have : (1 + t ^ 2) ^ 3 ≤ (3 * Real.exp (t ^ 2 / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    calc (1 + t ^ 2) ^ 3 ≤ (3 * Real.exp (t ^ 2 / 3)) ^ 3 := this
      _ = 27 * Real.exp (t ^ 2 / 3) ^ 3 := by ring
      _ = 27 * Real.exp (t ^ 2) := by rw [h3]
  have h5 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have h6 : (1 + t) ^ 6 ≤ 8 * (1 + t ^ 2) ^ 3 := by
    have : ((1 + t) ^ 2) ^ 3 ≤ (2 * (1 + t ^ 2)) ^ 3 := pow_le_pow_left₀ (by positivity) h5 3
    calc (1 + t) ^ 6 = ((1 + t) ^ 2) ^ 3 := by ring
      _ ≤ (2 * (1 + t ^ 2)) ^ 3 := this
      _ = 8 * (1 + t ^ 2) ^ 3 := by ring
  have h7 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ (1 + t) ^ 6 := by
    have a : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    have b : (1 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 3 * (1 + t ^ 2) ≤ (1 + t) ^ 3 * (1 + t) ^ 2 := by gcongr
      _ = (1 + t) ^ 5 * 1 := by ring
      _ ≤ (1 + t) ^ 5 * (1 + t) := by gcongr
      _ = (1 + t) ^ 6 := by ring
  have h8 : Real.exp (t ^ 2) ≤ Real.exp (Real.pi * t ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three, sq_nonneg t]
  have h9 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ 216 * Real.exp (Real.pi * t ^ 2) := by linarith
  have h10 : Real.exp (Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc (1 + t) ^ 3 * ((1 + t ^ 2) * Real.exp (-Real.pi * t ^ 2))
      = ((1 + t) ^ 3 * (1 + t ^ 2)) * Real.exp (-Real.pi * t ^ 2) := by ring
    _ ≤ (216 * Real.exp (Real.pi * t ^ 2)) * Real.exp (-Real.pi * t ^ 2) := by gcongr
    _ = 216 := by rw [mul_assoc, h10, mul_one]

lemma Kf_nonneg (w : ℂ) : 0 ≤ Kf w := by unfold Kf; positivity

lemma Kf_le (w : ℂ) : Kf w ≤ 216 := by
  have h := poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)
  have h1 : (1 : ℝ) ≤ (1 + ‖w‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg w])
  have h0 := Kf_nonneg w
  unfold Kf at *
  nlinarith

lemma Kf_cont : Continuous Kf := by unfold Kf; fun_prop

theorem Kf_int : Integrable Kf := by
  have hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < (3 : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num
  have h := (integrable_one_add_norm (E := ℂ) (μ := volume) hr).const_mul 216
  refine h.mono' Kf_cont.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Kf_nonneg w)]
  have hp : 0 < 1 + ‖w‖ := by positivity
  rw [Real.rpow_neg hp.le]
  have e : (1 + ‖w‖) ^ (3 : ℝ) = (1 + ‖w‖) ^ 3 := by norm_cast
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have := poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)
  unfold Kf
  linarith

lemma Ks_int (ε : ℝ) (hε : 0 < ε) (v : ℂ) : Integrable (fun w : ℂ => Kf (ε • (w - v))) :=
  (Kf_int.comp_smul hε.ne').comp_sub_right v

lemma Ks_integral (ε : ℝ) (hε : 0 < ε) (v : ℂ) :
    ∫ w : ℂ, Kf (ε • (w - v)) = (ε ^ 2)⁻¹ * ∫ w, Kf w := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun u : ℂ => Kf (ε • u)) v
  rw [h1, Measure.integral_comp_smul volume Kf ε, Complex.finrank_real_complex, smul_eq_mul,
    abs_of_pos (by positivity)]

lemma gw_eq (ε : ℝ) (v w : ℂ) : gw ε v w = Real.exp (-Real.pi * ε ^ 2 * ‖w - v‖ ^ 2) := rfl

lemma Ks_eq (ε : ℝ) (hε : 0 < ε) (v w : ℂ) :
    Kf (ε • (w - v)) = (1 + (ε * ‖w - v‖) ^ 2) * gw ε v w := by
  have hn : ‖ε • (w - v)‖ = ε * ‖w - v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
  unfold Kf
  rw [hn, gw_eq]
  congr 2
  ring

lemma gw_pos (ε : ℝ) (v w : ℂ) : 0 < gw ε v w := Real.exp_pos _

lemma gw_le (ε : ℝ) (v w : ℂ) : gw ε v w ≤ 1 := by
  rw [gw_eq, Real.exp_le_one_iff]
  have : 0 ≤ Real.pi * ε ^ 2 * ‖w - v‖ ^ 2 := by positivity
  linarith

lemma gw_cont (ε : ℝ) (v : ℂ) : Continuous (gw ε v) := by
  have : gw ε v = fun w => Real.exp (-Real.pi * ε ^ 2 * ‖w - v‖ ^ 2) := rfl
  rw [this]; fun_prop

lemma continuous_firstGaussDeriv (ε : ℝ) (v c : ℂ) : Continuous (G1 ε v c) := by
  have h := gw_cont ε v
  have : G1 ε v c = fun w => -2 * Real.pi * ε ^ 2 * (((starRingEnd ℂ) c * (w - v)).re) * gw ε v w := rfl
  rw [this]
  exact ((continuous_const.mul (Complex.continuous_re.comp
    (continuous_const.mul (continuous_id.sub continuous_const))))).mul h

lemma continuous_secondGaussDeriv (ε : ℝ) (v c : ℂ) : Continuous (G2 ε v c) := by
  have h := gw_cont ε v
  have : G2 ε v c = fun w => (-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 *
      (((starRingEnd ℂ) c * (w - v)).re) ^ 2) * gw ε v w := rfl
  rw [this]
  exact (continuous_const.add (continuous_const.mul ((Complex.continuous_re.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).pow 2))).mul h

lemma re_le (c u : ℂ) : |((starRingEnd ℂ) c * u).re| ≤ ‖c‖ * ‖u‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]

lemma firstGaussDeriv_bound (ε : ℝ) (hε : 0 < ε) (v c w : ℂ) :
    |G1 ε v c w| ≤ 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) := by
  rw [Ks_eq ε hε]
  have hg := gw_pos ε v w
  have hr := re_le c (w - v)
  have hpi := Real.pi_pos
  set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef
  set u := ‖w - v‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have e : |G1 ε v c w| = 2 * Real.pi * ε ^ 2 * |r| * gw ε v w := by
    unfold G1
    rw [abs_mul, abs_mul, abs_of_pos hg, abs_of_nonpos (a := -2 * Real.pi * ε ^ 2)]
    · ring
    · have : 0 ≤ 2 * Real.pi * ε ^ 2 := by positivity
      linarith
  rw [e]
  have hx : ε * u ≤ 1 + (ε * u) ^ 2 := by nlinarith [sq_nonneg (ε * u - 1)]
  have h1 : 2 * Real.pi * ε ^ 2 * |r| ≤ 2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2) := by
    calc 2 * Real.pi * ε ^ 2 * |r| ≤ 2 * Real.pi * ε ^ 2 * (‖c‖ * u) := by gcongr
      _ = 2 * Real.pi * ε * ‖c‖ * (ε * u) := by ring
      _ ≤ 2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2) := by gcongr
  calc 2 * Real.pi * ε ^ 2 * |r| * gw ε v w
      ≤ (2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2)) * gw ε v w := by gcongr
    _ = 2 * Real.pi * ε * ‖c‖ * ((1 + (ε * u) ^ 2) * gw ε v w) := by ring

lemma two_pi_le : 2 * Real.pi ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]

lemma secondGaussDeriv_bound (ε : ℝ) (hε : 0 < ε) (v c w : ℂ) :
    |G2 ε v c w| ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) := by
  rw [Ks_eq ε hε]
  have hg := gw_pos ε v w
  have hr := re_le c (w - v)
  have hpi := Real.pi_pos
  set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef
  set u := ‖w - v‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hr2 : r ^ 2 ≤ ‖c‖ ^ 2 * u ^ 2 := by
    rw [← mul_pow, ← sq_abs r]
    exact pow_le_pow_left₀ (abs_nonneg r) hr 2
  have e : |G2 ε v c w| = |-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2| * gw ε v w := by
    unfold G2
    rw [abs_mul, abs_of_pos hg]
  rw [e]
  have h1 : |-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2|
      ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2) := by
    have a : 0 ≤ 2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 := by positivity
    have b : 0 ≤ 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2 := by positivity
    have c1 : 2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right two_pi_le (by positivity : 0 ≤ ε ^ 2 * ‖c‖ ^ 2)
      linarith
    have c2 : 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2 ≤ 4 * Real.pi ^ 2 * ε ^ 4 * (‖c‖ ^ 2 * u ^ 2) := by
      gcongr
    have e2 : 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2)
        = 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * (‖c‖ ^ 2 * u ^ 2) := by ring
    rw [e2, abs_le]
    constructor <;> linarith
  calc _ ≤ (4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2)) * gw ε v w := by gcongr
    _ = 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * ((1 + (ε * u) ^ 2) * gw ε v w) := by ring

theorem main : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ v c : ℂ,
    (∀ w, 0 ≤ gw ε v w ∧ gw ε v w ≤ 1) ∧ Continuous (gw ε v) ∧ Continuous (G1 ε v c) ∧ Continuous (G2 ε v c) ∧
    (∀ w, |G1 ε v c w| ≤ B * ε * ‖c‖) ∧ (∀ w, |G2 ε v c w| ≤ B * ‖c‖ ^ 2) ∧
    Integrable (fun w => |G1 ε v c w|) ∧ (∫ w, |G1 ε v c w|) ≤ B * ‖c‖ / ε ∧
    Integrable (fun w => |G2 ε v c w|) ∧ (∫ w, |G2 ε v c w|) ≤ B * ‖c‖ ^ 2 := by
  set I : ℝ := ∫ w, Kf w with hI
  have hI0 : 0 ≤ I := integral_nonneg Kf_nonneg
  have hP : 0 < 4 * Real.pi ^ 2 := by have := Real.pi_pos; positivity
  have hP2 := two_pi_le
  have h2P : 0 < 2 * Real.pi := by have := Real.pi_pos; positivity
  refine ⟨4 * Real.pi ^ 2 * (216 + I), by positivity, fun ε hε hε1 v c => ?_⟩
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hB1 : 4 * Real.pi ^ 2 * 216 ≤ 4 * Real.pi ^ 2 * (216 + I) := by gcongr; linarith
  have hB2 : 4 * Real.pi ^ 2 * I ≤ 4 * Real.pi ^ 2 * (216 + I) := by gcongr; linarith
  have hB3 : 2 * Real.pi * I ≤ 4 * Real.pi ^ 2 * I := by gcongr
  have hB4 : 2 * Real.pi * 216 ≤ 4 * Real.pi ^ 2 * 216 := by gcongr
  have hK := Ks_int ε hε v
  have hKI := Ks_integral ε hε v
  have hi1 : Integrable (fun w => |G1 ε v c w|) :=
    (hK.const_mul (2 * Real.pi * ε * ‖c‖)).mono' (continuous_firstGaussDeriv ε v c).abs.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact firstGaussDeriv_bound ε hε v c w)
  have hi2 : Integrable (fun w => |G2 ε v c w|) :=
    (hK.const_mul (4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2)).mono' (continuous_secondGaussDeriv ε v c).abs.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact secondGaussDeriv_bound ε hε v c w)
  refine ⟨fun w => ⟨(gw_pos ε v w).le, gw_le ε v w⟩, gw_cont ε v, continuous_firstGaussDeriv ε v c, continuous_secondGaussDeriv ε v c,
    fun w => ?_, fun w => ?_, hi1, ?_, hi2, ?_⟩
  · calc |G1 ε v c w| ≤ 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) := firstGaussDeriv_bound ε hε v c w
      _ ≤ 2 * Real.pi * ε * ‖c‖ * 216 := by gcongr; exact Kf_le _
      _ = (2 * Real.pi * 216) * ε * ‖c‖ := by ring
      _ ≤ (4 * Real.pi ^ 2 * (216 + I)) * ε * ‖c‖ := by gcongr; linarith
  · have he : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    calc |G2 ε v c w| ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) := secondGaussDeriv_bound ε hε v c w
      _ ≤ 4 * Real.pi ^ 2 * 1 * ‖c‖ ^ 2 * 216 :=
          mul_le_mul (by gcongr) (Kf_le _) (Kf_nonneg _) (by positivity)
      _ = (4 * Real.pi ^ 2 * 216) * ‖c‖ ^ 2 := by ring
      _ ≤ (4 * Real.pi ^ 2 * (216 + I)) * ‖c‖ ^ 2 := by gcongr
  · have h1 : (∫ w, |G1 ε v c w|) ≤ ∫ w, 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) :=
      integral_mono hi1 (hK.const_mul _) (fun w => firstGaussDeriv_bound ε hε v c w)
    rw [integral_const_mul, hKI, ← hI] at h1
    refine h1.trans (le_of_eq_of_le ?_ (?_ : (2 * Real.pi * I) * ‖c‖ / ε ≤ _))
    · field_simp
    · gcongr
      linarith
  · have h1 : (∫ w, |G2 ε v c w|) ≤ ∫ w, 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) :=
      integral_mono hi2 (hK.const_mul _) (fun w => secondGaussDeriv_bound ε hε v c w)
    rw [integral_const_mul, hKI, ← hI] at h1
    refine h1.trans (le_of_eq_of_le ?_ (?_ : (4 * Real.pi ^ 2 * I) * ‖c‖ ^ 2 ≤ _))
    · field_simp
    · gcongr

end GlobalTheory.CompanionTheory.ParsC.GaussB

import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicKappaLemmas

open UpperTheory.Esk

theorem nsq (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pos_den {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

theorem kap_of {z w : P} (h : 0 < z.1.im * w.1.im) :
    kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
  unfold kap
  rw [if_pos h]

theorem kap_of_not {z w : P} (h : ¬ 0 < z.1.im * w.1.im) : kap z w = 0 := by
  unfold kap
  rw [if_neg h]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem key {z w u : ℂ} (h1 : 0 < z.im * w.im) (h2 : 0 < w.im * u.im) :
    w.im ^ 2 * ‖z - conj u‖ ^ 2 ≤ ‖z - conj w‖ ^ 2 * ‖w - conj u‖ ^ 2 := by
  have h13 : 0 < z.im * u.im := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.im)]
  have hp : 0 ≤ z.im ^ 2 + 2 * z.im * w.im := by nlinarith [sq_nonneg z.im]
  have hq : 0 ≤ u.im ^ 2 + 2 * w.im * u.im := by nlinarith [sq_nonneg u.im]
  rw [nsq, nsq, nsq]
  nlinarith [sq_nonneg ((z.re - w.re) * (w.re - u.re) - w.im ^ 2),
    mul_nonneg (sq_nonneg (z.re - w.re)) hq, mul_nonneg (sq_nonneg (w.re - u.re)) hp,
    mul_nonneg (sq_nonneg w.im) h1.le, mul_nonneg (sq_nonneg w.im) h2.le,
    mul_nonneg (sq_nonneg w.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
    sq_nonneg (z.im * u.im)]

theorem p1 (z w : P) : 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z := by
  refine ⟨kap_nonneg z w, ?_, ?_⟩
  · by_cases h : 0 < z.1.im * w.1.im
    · rw [kap_of h, div_le_iff₀ (pos_den h), nsq]
      nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
    · rw [kap_of_not h]
      norm_num
  · have e2 : ‖w.1 - conj z.1‖ ^ 2 = ‖z.1 - conj w.1‖ ^ 2 := by
      rw [nsq, nsq]
      ring
    unfold kap
    rw [mul_comm w.1.im z.1.im, e2]

theorem p2 (z : P) : kap z z = 1 := by
  have h : 0 < z.1.im * z.1.im := mul_self_pos.mpr z.2
  rw [kap_of h, div_eq_one_iff_eq (pos_den h).ne', nsq]
  ring

theorem p3 (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  by_cases h1 : 0 < z.1.im * w.1.im
  · by_cases h2 : 0 < w.1.im * u.1.im
    · have h13 : 0 < z.1.im * u.1.im := by
        by_contra hc
        have hc := not_lt.mp hc
        nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.1.im)]
      have hA := pos_den h1
      have hB := pos_den h2
      have hC := pos_den h13
      have hk := mul_le_mul_of_nonneg_left (key h1 h2) h13.le
      rw [kap_of h1, kap_of h2, kap_of h13, div_mul_div_comm, mul_div_assoc', le_div_iff₀ hC,
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hA hB)]
      nlinarith [hk]
    · rw [kap_of_not h2, mul_zero]
      exact mul_nonneg (by norm_num) (kap_nonneg z u)
  · rw [kap_of_not h1, zero_mul]
    exact mul_nonneg (by norm_num) (kap_nonneg z u)

theorem p4 (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  by_cases h : 0 < z.1.im * w.1.im
  · rw [kap_of h, div_mul_eq_mul_div, div_le_iff₀ (pos_den h), nsq]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith [h, hw]
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.mpr hw.le)]
    · have hz : 0 < z.1.im := by nlinarith [h, hw]
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)), mul_nonneg hz.le (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [kap_of_not h, zero_mul]
    positivity

theorem p5 : Continuous (fun p : P × P => kap p.1 p.2) := by
  have hv1 : Continuous (fun p : P × P => p.1.1) := continuous_subtype_val.comp continuous_fst
  have hv2 : Continuous (fun p : P × P => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun p : P × P => p.1.1.im * p.2.1.im) :=
    (Complex.continuous_im.comp hv1).mul (Complex.continuous_im.comp hv2)
  have hd : Continuous (fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2) :=
    ((hv1.sub (Complex.continuous_conj.comp hv2)).norm).pow 2
  have hopen : IsOpen {p : P × P | 0 < p.1.1.im * p.2.1.im} := isOpen_lt continuous_const hc
  have hclosed : IsClosed {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
    have e : {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (Ne.symm (mul_ne_zero p.1.2 p.2.2))⟩
    rw [e]
    exact isClosed_le continuous_const hc
  have hfr : frontier {p : P × P | 0 < p.1.1.im * p.2.1.im} = ∅ := by
    rw [frontier, hclosed.closure_eq, hopen.interior_eq, Set.sdiff_self]
  show Continuous (fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0)
  apply continuous_if
  · intro a ha
    simp [hfr] at ha
  · rw [hclosed.closure_eq]
    exact ((continuous_const.mul hc).continuousOn).div hd.continuousOn
      (fun p hp => (pos_den (z := p.1.1) (w := p.2.1) hp).ne')
  · exact continuousOn_const

theorem p6 (z : P) : ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hdet : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using z.2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, rfl, Subtype.ext ?_⟩
  rw [coe_smul]
  show num (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I /
    den (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I = z.1
  have h00 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 0 = z.1.im := rfl
  have h01 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 1 = z.1.re := rfl
  have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 0 = 0 := rfl
  have h11 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 1 = 1 := rfl
  rw [num, den, h00, h01, h10, h11]
  apply Complex.ext <;> simp

end UpperTheory.Esk.HyperbolicKappaLemmas

namespace UpperTheory.Esk

theorem hyperbolic_kappa_properties_proof : B1c := by
  unfold B1c
  exact ⟨HyperbolicKappaLemmas.p1, HyperbolicKappaLemmas.p2, HyperbolicKappaLemmas.p3, HyperbolicKappaLemmas.p4, HyperbolicKappaLemmas.p5, HyperbolicKappaLemmas.p6⟩

end UpperTheory.Esk

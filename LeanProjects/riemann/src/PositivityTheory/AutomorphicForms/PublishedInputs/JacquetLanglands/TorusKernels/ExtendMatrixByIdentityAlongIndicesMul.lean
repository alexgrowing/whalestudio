import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix Real
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingFormulaLemmas

open UpperTheory.Esk

def mkP (t : ℂ) (h : t.im ≠ 0) : P := ⟨t, h⟩

theorem extendHalfPlane_coe_point (f : P → ℂ) (z : P) : ext1 f z.1 = f z := by
  unfold ext1; rw [dif_pos z.2]; rfl

theorem extendHalfPlane_of_im_ne_zero (f : P → ℂ) {t : ℂ} (h : t.im ≠ 0) : ext1 f t = f (mkP t h) := by
  unfold ext1; rw [dif_pos h]; rfl

theorem extendMatrixByIdentityAlongIndices_mul (f g : P → ℂ) {t : ℂ} (h : t.im ≠ 0) :
    ext1 (fun w => g w * f w) t = g (mkP t h) * f (mkP t h) := by
  unfold ext1; rw [dif_pos h]; rfl

theorem cont_of_hol {f : P → ℂ} (hf : Hol1 f) : Continuous f := by
  have h1 : Continuous (fun z : P => ext1 f z.1) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun z => z.2)
  convert h1 using 1
  funext z
  exact (extendHalfPlane_coe_point f z).symm

theorem integ (B1b' : B1b) (B1c' : B1c) (B6' : B6) {k : ℕ} (hk : 4 ≤ k) {f : P → ℂ}
    (hc : Continuous f) {C : ℝ} (hC : ∀ z : P, ‖f z‖ * |z.1.im| ^ ((k : ℝ) / 2) ≤ C) (z : P) :
    Integrable (fun w => q1 k z w * f w) := by
  obtain ⟨C6, hC6⟩ := B6' k hk
  have hkap_cont : Continuous (fun w => kap z w) :=
    B1c'.2.2.2.2.1.comp (continuous_const.prodMk continuous_id)
  have hqc : Continuous (fun w => q1 k z w) :=
    (B1b'.2.2.2.2.2.2.2.1 k).comp (continuous_const.prodMk continuous_id)
  have hbnd_int : Integrable (fun w => kap z w ^ ((k : ℝ) / 2)) := by
    have hm : Continuous (fun w => kap z w ^ ((k : ℝ) / 2)) :=
      hkap_cont.rpow_const (fun _ => Or.inr (by positivity))
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (B1c'.1 z w).1 _)]
    exact lt_of_le_of_lt (hC6 z).1 ENNReal.coe_lt_top
  have hz : 0 < |z.1.im| := abs_pos.mpr z.2
  have hA : 0 ≤ ((k : ℝ) - 1) / (4 * π) := by
    apply div_nonneg _ (by positivity)
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine (hbnd_int.const_mul (((k : ℝ) - 1) / (4 * π) * C / |z.1.im| ^ ((k : ℝ) / 2))).mono'
    (hqc.mul hc).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun w => ?_
  have h6 := B1b'.2.2.2.2.2.1 k z w (by omega)
  have hze : 0 < |z.1.im| ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hz _
  have hkp : 0 ≤ kap z w ^ ((k : ℝ) / 2) := Real.rpow_nonneg (B1c'.1 z w).1 _
  have hq : ‖q1 k z w‖ = ((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2)
      / |z.1.im| ^ ((k : ℝ) / 2) := by
    rw [eq_div_iff hze.ne']; exact h6
  rw [norm_mul, hq]
  calc ((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2)
        / |z.1.im| ^ ((k : ℝ) / 2) * ‖f w‖
      = (((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) / |z.1.im| ^ ((k : ℝ) / 2)) *
          (‖f w‖ * |w.1.im| ^ ((k : ℝ) / 2)) := by ring
    _ ≤ (((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) / |z.1.im| ^ ((k : ℝ) / 2)) * C :=
        mul_le_mul_of_nonneg_left (hC w) (div_nonneg (mul_nonneg hA hkp) hze.le)
    _ = ((k : ℝ) - 1) / (4 * π) * C / |z.1.im| ^ ((k : ℝ) / 2) * kap z w ^ ((k : ℝ) / 2) := by ring

theorem hol_comp (g : GL (Fin 2) ℝ) (k : ℕ) {f : P → ℂ} (hf : Hol1 f) :
    Hol1 (fun w => f (g • w) / j1 k g w) := by
  have hc0 : ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (abs_pos.mpr g.det_ne_zero) _).ne'
  have hnum : Differentiable ℂ (num g) := by
    intro t; unfold num; fun_prop
  have hden : Differentiable ℂ (den g) := by
    intro t; unfold den; fun_prop
  have hmob : DifferentiableOn ℂ (fun t => num g t / den g t) {t : ℂ | t.im ≠ 0} :=
    fun t ht => ((hnum t).div (hden t) (den_ne g ht)).differentiableWithinAt
  have hmaps : Set.MapsTo (fun t => num g t / den g t) {t : ℂ | t.im ≠ 0} {t | t.im ≠ 0} := by
    intro t ht
    exact (g • mkP t ht).2
  have h1 : DifferentiableOn ℂ (fun t => ext1 f (num g t / den g t) /
      (den g t ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ))) {t | t.im ≠ 0} := by
    refine (hf.comp hmob hmaps).div ?_ ?_
    · exact fun t _ => (((hden t).pow k).mul_const _).differentiableWithinAt
    · intro t ht; exact mul_ne_zero (pow_ne_zero _ (den_ne g ht)) hc0
  refine h1.congr ?_
  intro t ht
  rw [extendHalfPlane_of_im_ne_zero _ ht]
  show f (g • mkP t ht) / j1 k g (mkP t ht) = _
  rw [← extendHalfPlane_coe_point f (g • mkP t ht), coe_smul]
  rfl

theorem memb (B1a' : B1a) (g : GL (Fin 2) ℝ) : MeasurableEmbedding (fun z : P => g • z) := by
  let h : P ≃ₜ P :=
    { toEquiv := MulAction.toPerm g, continuous_toFun := (B1a'.2.2 g).1,
      continuous_invFun := (B1a'.2.2 g⁻¹).1 }
  exact h.measurableEmbedding

theorem wim (s : ℂ) :
    (Complex.I * (1 + s) / (1 - s)).im = (1 - Complex.normSq s) / Complex.normSq (1 - s) := by
  rw [Complex.div_im, Complex.normSq_apply s]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  ring

theorem disc (s : ℂ) (hs : ‖s‖ < 1) : (1 - s) ≠ 0 ∧ 0 < (Complex.I * (1 + s) / (1 - s)).im := by
  have h1 : (1 - s) ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination -h
    rw [this, norm_one] at hs
    exact lt_irrefl _ hs
  refine ⟨h1, ?_⟩
  rw [wim]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg s]
  · exact Complex.normSq_pos.mpr h1

theorem pt_eq (f : P → ℂ) (m : ℕ) {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ext1 (fun w => q1 (m + 2) iP w * f w)
      (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) =
    ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) *
      (ext1 f (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) /
        (1 - circleMap 0 r θ) ^ (m + 2)) := by
  have hns : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
  obtain ⟨h1s, hwim⟩ := disc (circleMap 0 r θ) (by rw [hns]; exact hr1)
  have hsq : Complex.normSq (circleMap 0 r θ) = r ^ 2 := by rw [Complex.normSq_eq_norm_sq, hns]
  set s := circleMap 0 r θ with hs
  set w := Complex.I * (1 + s) / (1 - s) with hw
  rw [extendMatrixByIdentityAlongIndices_mul f _ hwim.ne', extendHalfPlane_of_im_ne_zero f hwim.ne']
  have hqi : q1 (m + 2) iP (mkP w hwim.ne') =
      (((m + 2 : ℕ) : ℂ) - 1) / (4 * π) * ((w - conj w) / (Complex.I - conj w)) ^ (m + 2) := by
    unfold q1
    rw [if_pos (by show 0 < Complex.I.im * w.im; rw [Complex.I_im, one_mul]; exact hwim)]
    rfl
  have hcs : s * conj s = (r : ℂ) ^ 2 := by rw [Complex.mul_conj, hsq]; push_cast; ring
  have h1c : (1 - conj s) ≠ 0 := by
    intro h; apply h1s
    have := congrArg conj h
    simpa using this
  have hcw : conj w = -Complex.I * (1 + conj s) / (1 - conj s) := by
    rw [hw, map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hD : Complex.I - conj w = 2 * Complex.I / (1 - conj s) := by
    rw [hcw]; field_simp; ring
  have hN : w - conj w = 2 * Complex.I * (1 - s * conj s) / ((1 - s) * (1 - conj s)) := by
    rw [hcw, hw]; field_simp; ring
  have hratio : (w - conj w) / (Complex.I - conj w) = (1 - (r : ℂ) ^ 2) / (1 - s) := by
    rw [hN, hD, hcs]; field_simp
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hr2 : (1 - (r : ℂ) ^ 2) ≠ 0 := by
    have : (1 - r ^ 2 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  rw [hqi, hratio, div_pow]
  have key : ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((((m + 2 : ℕ) : ℂ) - 1) / (4 * π)) *
      (1 - (r : ℂ) ^ 2) ^ (m + 2) = ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← key]
  ring

theorem mv {G : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hG : DiffContOnCl ℂ G (Metric.ball 0 r)) :
    ∫ θ in Set.Ioo (-π) π, G (circleMap 0 r θ) = 2 * (π : ℂ) * G 0 := by
  have h1 := (show DiffContOnCl ℂ G (Metric.ball 0 |r|) by rwa [abs_of_pos hr]).circleAverage
  have hper : Function.Periodic (fun θ => G (circleMap 0 r θ)) (2 * π) := by
    intro θ
    show G (circleMap 0 r (θ + 2 * π)) = G (circleMap 0 r θ)
    rw [periodic_circleMap 0 r θ]
  have h2 := hper.intervalIntegral_add_eq (-π) 0
  have e1 : -π + 2 * π = π := by ring
  rw [e1, zero_add] at h2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]), h2]
  rw [Real.circleAverage_def, Complex.real_smul] at h1
  rw [← h1]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  push_cast
  field_simp

theorem radial (m : ℕ) :
    ∫ r in Set.Ioo (0 : ℝ) 1, ((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m = 1 / (2 * π) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (m + 1) / (2 * π))
      (((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    refine ((h1.pow (m + 1)).neg.div_const (2 * π)).congr_deriv ?_
    have hπ : π ≠ 0 := pi_ne_zero
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hi : IntervalIntegrable (fun x : ℝ => ((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => ((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp
  ring

theorem at_i (B1b' : B1b) (B1c' : B1c) (B2' : B2) (B6' : B6) {k : ℕ} (hk : 4 ≤ k) {f : P → ℂ}
    (hf : Hol1 f) {C : ℝ} (hC : ∀ z : P, ‖f z‖ * |z.1.im| ^ ((k : ℝ) / 2) ≤ C) :
    ∫ w, q1 k iP w * f w = f iP := by
  have hint := integ B1b' B1c' B6' hk (cont_of_hol hf) hC iP
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hvan : ∀ w : P, w.1.im < 0 → q1 (m + 2) iP w * f w = 0 := by
    intro w hw
    have : ¬ (0 < iP.1.im * w.1.im) := by
      show ¬ (0 < Complex.I.im * w.1.im)
      rw [Complex.I_im, one_mul, not_lt]; exact hw.le
    unfold q1
    rw [if_neg this, zero_mul]
  obtain ⟨hIO, heq⟩ := B2' (fun w => q1 (m + 2) iP w * f w) hvan hint
  rw [heq]
  have hS : MeasurableSet (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hpt : Set.EqOn (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
        ext1 (fun w => q1 (m + 2) iP w * f w)
          (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)))
      (fun p : ℝ × ℝ => ((((m : ℝ) + 1) / π * p.1 * (1 - p.1 ^ 2) ^ m : ℝ) : ℂ) *
        (ext1 f (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)) /
          (1 - circleMap 0 p.1 p.2) ^ (m + 2)))
      (Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π) := by
    intro p hp
    exact pt_eq f m hp.1.1 hp.1.2
  rw [setIntegral_congr_fun hS hpt]
  have hI2 := hIO.congr_fun hpt hS
  rw [Measure.volume_eq_prod] at hI2 ⊢
  rw [setIntegral_prod _ hI2]
  dsimp only
  have hGd : DifferentiableOn ℂ
      (fun s : ℂ => ext1 f (Complex.I * (1 + s) / (1 - s)) / (1 - s) ^ (m + 2)) (Metric.ball 0 1) := by
    have hU : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
    have hw : DifferentiableOn ℂ (fun s : ℂ => Complex.I * (1 + s) / (1 - s)) (Metric.ball 0 1) := by
      intro s hs
      rw [mem_ball_zero_iff] at hs
      exact (DifferentiableAt.div (by fun_prop) (by fun_prop) (disc s hs).1).differentiableWithinAt
    have hmaps : Set.MapsTo (fun s : ℂ => Complex.I * (1 + s) / (1 - s)) (Metric.ball 0 1)
        {t : ℂ | t.im ≠ 0} := by
      intro s hs
      rw [mem_ball_zero_iff] at hs
      exact (disc s hs).2.ne'
    refine (hf.comp hw hmaps).div ?_ ?_
    · intro s _; exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (1 - s) ^ (m + 2)) s).differentiableWithinAt
    · intro s hs
      rw [mem_ball_zero_iff] at hs
      exact pow_ne_zero _ (disc s hs).1
  have hG0 : (fun s : ℂ => ext1 f (Complex.I * (1 + s) / (1 - s)) / (1 - s) ^ (m + 2)) 0 = f iP := by
    simp only [add_zero, sub_zero, mul_one, div_one, one_pow]
    exact extendHalfPlane_coe_point f iP
  have hin : ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∫ θ in Set.Ioo (-π) π,
      ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) *
        (ext1 f (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) /
          (1 - circleMap 0 r θ) ^ (m + 2)) =
      ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) * (2 * (π : ℂ) * f iP) := by
    intro r hr
    rw [integral_const_mul, ← hG0]
    congr 1
    refine mv (G := fun s : ℂ => ext1 f (Complex.I * (1 + s) / (1 - s)) / (1 - s) ^ (m + 2)) hr.1 ?_
    refine (hGd.mono ?_).diffContOnCl
    rw [closure_ball 0 hr.1.ne']
    exact Metric.closedBall_subset_ball hr.2
  rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_mul_const, integral_complex_ofReal, radial]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  push_cast
  field_simp

end UpperTheory.Esk.ReproducingFormulaLemmas

open UpperTheory.Esk.ReproducingFormulaLemmas in
theorem UpperTheory.Esk.reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B2 → UpperTheory.Esk.B6 → UpperTheory.Esk.B3 := by
  intro hB1a hB1b hB1c hB2 hB6 k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  refine ⟨integ hB1b hB1c hB6 hk (cont_of_hol hf) hC z, ?_⟩
  obtain ⟨g, -, -, hg⟩ := hB1c.2.2.2.2.2 z
  subst hg
  have hf' : Hol1 (fun w => f (g • w) / j1 k g w) := hol_comp g k hf
  have hC' : ∀ w : UpperTheory.Esk.P, ‖f (g • w) / j1 k g w‖ * |w.1.im| ^ ((k : ℝ) / 2) ≤ C := by
    intro w
    have h5 := hB1b.2.2.2.2.1 k g w
    have hj : ‖j1 k g w‖ ≠ 0 := norm_ne_zero_iff.mpr (hB1b.2.1 k g w)
    calc ‖f (g • w) / j1 k g w‖ * |w.1.im| ^ ((k : ℝ) / 2)
        = ‖f (g • w)‖ * |(g • w).1.im| ^ ((k : ℝ) / 2) := by
          rw [← h5, norm_div]; field_simp
      _ ≤ C := hC _
  have h_i := at_i hB1b hB1c hB2 hB6 hk hf' hC'
  rw [← (hB1a.2.2 g).2.integral_comp (memb hB1a g) (fun w => q1 k (g • iP) w * f w)]
  have hpt : ∀ w, q1 k (g • iP) (g • w) * f (g • w) = j1 k g iP * (q1 k iP w * (f (g • w) / j1 k g w)) := by
    intro w
    have h3 := hB1b.2.2.1 k g iP w
    have hj := hB1b.2.1 k g w
    calc q1 k (g • iP) (g • w) * f (g • w)
        = (q1 k (g • iP) (g • w) * j1 k g w) * f (g • w) / j1 k g w := by field_simp
      _ = (j1 k g iP * q1 k iP w) * f (g • w) / j1 k g w := by rw [h3]
      _ = _ := by ring
  simp_rw [hpt]
  rw [integral_const_mul, h_i]
  have hj := hB1b.2.1 k g iP
  field_simp

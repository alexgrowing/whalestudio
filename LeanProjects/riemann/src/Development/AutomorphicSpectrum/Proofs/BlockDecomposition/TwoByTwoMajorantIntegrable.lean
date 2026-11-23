import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Set Filter

namespace GlobalTheory.CompanionTheory.TwoByTwoMajorant

theorem integrable_abs_rpow_div {a : ℝ} (h1 : -1 < a) (h2 : a < 1) :
    Integrable (fun w : ℝ => |w| ^ a / (1 + |w|) ^ 2) := by
  set f : ℝ → ℝ := fun w => |w| ^ a / (1 + |w|) ^ 2 with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hA : IntegrableOn f (Ioc 0 1) := by
    have h0 : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine Integrable.mono' h0 hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hnn : 0 ≤ x ^ a := by positivity
    simp only [hf]
    rw [abs_of_pos hx0, Real.norm_of_nonneg (by positivity)]
    exact div_le_self hnn (one_le_pow₀ (by linarith))
  have hB : IntegrableOn f (Ioi 1) := by
    have h0 := integrableOn_Ioi_rpow_of_lt (a := a - 2) (by linarith) (zero_lt_one)
    refine Integrable.mono' h0 hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hnn : 0 ≤ x ^ a := by positivity
    simp only [hf]
    rw [abs_of_pos hx0, Real.norm_of_nonneg (by positivity), Real.rpow_sub hx0, Real.rpow_two]
    refine div_le_div_of_nonneg_left hnn (by positivity) ?_
    nlinarith
  have hC : IntegrableOn f (Ioi 0) := by
    have : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [this]
    exact hA.union hB
  have hD : IntegrableOn f (Iio 0) := by
    have hp := Measure.measurePreserving_neg (volume : Measure ℝ)
    have he := (MeasurableEquiv.neg ℝ).measurableEmbedding
    have : IntegrableOn (f ∘ (Neg.neg : ℝ → ℝ)) ((Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0) :=
      (hp.integrableOn_comp_preimage he).2 hC
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by
      ext x; simp
    have hcomp : f ∘ (Neg.neg : ℝ → ℝ) = f := by
      funext x; simp [hf]
    rwa [hpre, hcomp] at this
  have hE : IntegrableOn f (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    exact hD
  have := hE.union hC
  rwa [Iic_union_Ioi, integrableOn_univ] at this

def phi (σ w : ℝ) : ℝ := |w| ^ (1 - σ) / (1 + |w|) ^ 2

def aa (σ x : ℝ) : ℝ := |x| ^ (σ - 2) / (1 + |x|) ^ 2

def bb (p : ℝ) : ℝ := 1 / (1 + |p|) ^ 2

def G0 (σ x p y u : ℝ) : ℝ := aa σ x * bb p * phi σ (u - y * p / x)

theorem phi_nonneg (σ w : ℝ) : 0 ≤ phi σ w := by unfold phi; positivity
theorem aa_nonneg (σ x : ℝ) : 0 ≤ aa σ x := by unfold aa; positivity
theorem bb_nonneg (p : ℝ) : 0 ≤ bb p := by unfold bb; positivity
theorem majorant_integrand_nonneg (σ x p y u : ℝ) : 0 ≤ G0 σ x p y u :=
  mul_nonneg (mul_nonneg (aa_nonneg _ _) (bb_nonneg _)) (phi_nonneg _ _)

theorem core {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 4 ≤ N) {x p y u n : ℝ}
    (hx : x ≠ 0) (hyx : |y| ≤ |x|) (hxn : |x| ≤ n) (hpn : |p| ≤ n) :
    |x * u - p * y| ^ (-1 - σ) * (x ^ 2 + y ^ 2) ^ ((2 * σ - 1) / 2) /
      ((1 + n) ^ N * (1 + (x ^ 2 + y ^ 2) ^ ((1 : ℝ) / 2) / |x * u - p * y|) ^ N)
      ≤ 2 * G0 σ x p y u := by
  have hG := majorant_integrand_nonneg σ x p y u
  by_cases hD : x * u - p * y = 0
  · rw [hD, abs_zero, Real.zero_rpow (by linarith)]
    simpa using hG
  set w : ℝ := u - y * p / x with hw
  have hDw : x * u - p * y = x * w := by
    rw [hw]; field_simp
  have hw0 : w ≠ 0 := by
    intro h; apply hD; rw [hDw, h, mul_zero]
  set A : ℝ := |x| with hA
  set W : ℝ := |w| with hW
  have hA0 : 0 < A := abs_pos.2 hx
  have hW0 : 0 < W := abs_pos.2 hw0
  have hDabs : |x * u - p * y| = A * W := by rw [hDw, abs_mul]
  have hsq : x ^ 2 = A ^ 2 := (sq_abs x).symm
  have hysq : y ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hyx 2
  set R : ℝ := x ^ 2 + y ^ 2 with hR
  have hRlo : A ^ 2 ≤ R := by rw [hR, hsq]; nlinarith [sq_nonneg y]
  have hRhi : R ≤ 2 * A ^ 2 := by rw [hR, hsq]; linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hR0 : 0 < R := lt_of_lt_of_le hA2 hRlo

  have t1 : R ^ ((2 * σ - 1) / 2) ≤ 2 * A ^ (2 * σ - 1) := by
    have hρ1 : 1 ≤ R / A ^ 2 := (one_le_div hA2).2 hRlo
    have hρ2 : R / A ^ 2 ≤ 2 := (div_le_iff₀ hA2).2 hRhi
    have hsplit : R = A ^ 2 * (R / A ^ 2) := by field_simp
    have hA2e : (A ^ 2) ^ ((2 * σ - 1) / 2) = A ^ (2 * σ - 1) := by
      rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA0.le]
      congr 1
      push_cast
      ring
    have hρe : (R / A ^ 2) ^ ((2 * σ - 1) / 2) ≤ 2 := by
      calc (R / A ^ 2) ^ ((2 * σ - 1) / 2) ≤ (R / A ^ 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
        _ = R / A ^ 2 := Real.rpow_one _
        _ ≤ 2 := hρ2
    calc R ^ ((2 * σ - 1) / 2) = (A ^ 2 * (R / A ^ 2)) ^ ((2 * σ - 1) / 2) := by rw [← hsplit]
      _ = A ^ (2 * σ - 1) * (R / A ^ 2) ^ ((2 * σ - 1) / 2) := by
          rw [Real.mul_rpow hA2.le (by positivity), hA2e]
      _ ≤ A ^ (2 * σ - 1) * 2 := by
          exact mul_le_mul_of_nonneg_left hρe (by positivity)
      _ = 2 * A ^ (2 * σ - 1) := by ring

  have t2 : A ≤ R ^ ((1 : ℝ) / 2) := by
    have : (A ^ 2) ^ ((1 : ℝ) / 2) = A := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hA0.le]
    calc A = (A ^ 2) ^ ((1 : ℝ) / 2) := this.symm
      _ ≤ R ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hA2.le hRlo (by norm_num)
  have hn0 : 0 ≤ n := le_trans hA0.le hxn

  have t3 : ((1 + W) / W) ^ 2 ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N := by
    have hb : (1 + W) / W ≤ 1 + R ^ ((1 : ℝ) / 2) / (A * W) := by
      have e1 : (1 + W) / W = 1 + A / (A * W) := by
        field_simp
        ring
      rw [e1]
      have : A / (A * W) ≤ R ^ ((1 : ℝ) / 2) / (A * W) :=
        div_le_div_of_nonneg_right t2 (by positivity)
      linarith
    have hb1 : 1 ≤ 1 + R ^ ((1 : ℝ) / 2) / (A * W) := by
      have : 0 ≤ R ^ ((1 : ℝ) / 2) / (A * W) := by positivity
      linarith
    calc ((1 + W) / W) ^ 2 ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N :=
          pow_le_pow_right₀ hb1 (by omega)
  have t4 : (1 + A) ^ 2 * (1 + |p|) ^ 2 ≤ (1 + n) ^ N := by
    have e1 : (1 + A) ^ 2 ≤ (1 + n) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have e2 : (1 + |p|) ^ 2 ≤ (1 + n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc (1 + A) ^ 2 * (1 + |p|) ^ 2 ≤ (1 + n) ^ 2 * (1 + n) ^ 2 :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = (1 + n) ^ 4 := by ring
      _ ≤ (1 + n) ^ N := pow_le_pow_right₀ (by linarith) hN
  rw [hDabs]
  have hP : (A * W) ^ (-1 - σ) * R ^ ((2 * σ - 1) / 2)
      ≤ (A ^ (-1 - σ) * W ^ (-1 - σ)) * (2 * A ^ (2 * σ - 1)) := by
    rw [Real.mul_rpow hA0.le hW0.le]
    exact mul_le_mul_of_nonneg_left t1 (by positivity)
  have hQ : ((1 + A) ^ 2 * (1 + |p|) ^ 2) * ((1 + W) / W) ^ 2
      ≤ (1 + n) ^ N * (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N :=
    mul_le_mul t4 t3 (by positivity) (by positivity)
  refine (div_le_div₀ (by positivity) hP (by positivity) hQ).trans (le_of_eq ?_)
  have eA : A ^ (σ - 2) = A ^ (-1 - σ) * A ^ (2 * σ - 1) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  have eW : W ^ (1 - σ) = W ^ (-1 - σ) * W ^ 2 := by
    rw [← Real.rpow_natCast W 2, ← Real.rpow_add hW0]; congr 1; push_cast; ring
  unfold G0 aa bb phi
  rw [← hw, ← hA, ← hW, eA, eW]
  field_simp

def Gi (σ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if |q.2.1| ≤ |q.1.1| then G0 σ q.1.1 q.1.2 q.2.1 q.2.2 else 0

theorem Gi_nonneg (σ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : 0 ≤ Gi σ q := by
  unfold Gi
  split_ifs
  · exact majorant_integrand_nonneg _ _ _ _ _
  · exact le_rfl

theorem measurable_Gi (σ : ℝ) : Measurable (Gi σ) := by
  unfold Gi
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) ?_ measurable_const
  unfold G0 aa bb phi
  fun_prop

theorem lintegral_Gi_lt_top {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∫⁻ q, ENNReal.ofReal (Gi σ q) < ⊤ := by
  have hmG : Measurable fun q => ENNReal.ofReal (Gi σ q) :=
    ENNReal.measurable_ofReal.comp (measurable_Gi σ)
  set K : ENNReal := ∫⁻ w : ℝ, ENNReal.ofReal (phi σ w) with hK
  have hphi : Integrable (phi σ) :=
    integrable_abs_rpow_div (a := 1 - σ) (by linarith) (by linarith)
  have hKt : K < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => phi_nonneg σ w)).1 hphi.2
  have inner : ∀ xp : ℝ × ℝ, ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (Gi σ (xp, z))
      = ENNReal.ofReal (aa σ xp.1 * bb xp.2 * (2 * |xp.1|)) * K := by
    intro xp
    obtain ⟨x, p⟩ := xp
    have hm : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (Gi σ ((x, p), z)) :=
      hmG.comp (by fun_prop)
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
    have hy : ∀ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (Gi σ ((x, p), (y, u)))
        = (Icc (-|x|) |x|).indicator (fun _ => ENNReal.ofReal (aa σ x * bb p) * K) y := by
      intro y
      by_cases hyx : |y| ≤ |x|
      · rw [indicator_of_mem (show y ∈ Icc (-|x|) |x| from abs_le.1 hyx)]
        simp only [Gi, hyx, if_true, G0]
        have hc : 0 ≤ aa σ x * bb p := mul_nonneg (aa_nonneg _ _) (bb_nonneg _)
        simp_rw [ENNReal.ofReal_mul hc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (phi σ w))]
      · rw [indicator_of_notMem (show y ∉ Icc (-|x|) |x| from fun h => hyx (abs_le.2 h))]
        simp [Gi, hyx]
    simp_rw [hy]
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    have hc : 0 ≤ aa σ x * bb p := mul_nonneg (aa_nonneg _ _) (bb_nonneg _)
    rw [show |x| - -|x| = 2 * |x| by ring, ENNReal.ofReal_mul hc]
    ring
  have hE : Integrable (fun w : ℝ => |w| ^ (σ - 1) / (1 + |w|) ^ 2) :=
    integrable_abs_rpow_div (by linarith) (by linarith)
  have hB : Integrable bb := by
    have hb : bb = fun w : ℝ => |w| ^ (0 : ℝ) / (1 + |w|) ^ 2 := by
      funext w
      simp [bb]
    rw [hb]
    exact integrable_abs_rpow_div (by norm_num) (by norm_num)
  have hprod := (hE.mul_prod hB).const_mul 2
  have hEq : ∀ x : ℝ, aa σ x * (2 * |x|) = 2 * (|x| ^ (σ - 1) / (1 + |x|) ^ 2) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [aa, Real.zero_rpow (show σ - 1 ≠ 0 by linarith)]
    · have hA : 0 < |x| := abs_pos.2 hx
      have : |x| ^ (σ - 1) = |x| ^ (σ - 2) * |x| := by
        rw [← Real.rpow_add_one hA.ne']; congr 1; ring
      rw [this, aa]
      ring
  have hfin : ∫⁻ xp : ℝ × ℝ, ENNReal.ofReal (aa σ xp.1 * bb xp.2 * (2 * |xp.1|)) < ⊤ := by
    have hnn : (0 : (ℝ × ℝ) → ℝ) ≤ᵐ[volume.prod volume]
        (fun z : ℝ × ℝ => 2 * ((|z.1| ^ (σ - 1) / (1 + |z.1|) ^ 2) * bb z.2)) :=
      ae_of_all _ fun z => mul_nonneg zero_le_two
        (mul_nonneg (by positivity) (bb_nonneg _))
    have := (hasFiniteIntegral_iff_ofReal hnn).1 hprod.2
    rw [Measure.volume_eq_prod]
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun z => ?_
    congr 1
    have := hEq z.1
    calc aa σ z.1 * bb z.2 * (2 * |z.1|) = (aa σ z.1 * (2 * |z.1|)) * bb z.2 := by ring
      _ = _ := by rw [this]; ring
  rw [Measure.volume_eq_prod, lintegral_prod _ hmG.aemeasurable]
  simp_rw [inner]
  rw [lintegral_mul_const' _ _ hKt.ne]
  exact ENNReal.mul_lt_top hfin hKt

theorem integrable_Gi {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : Integrable (Gi σ) :=
  ⟨(measurable_Gi σ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => Gi_nonneg σ q)).2
      (lintegral_Gi_lt_top h0 h1)⟩

def coord : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

theorem coord_mp : MeasurePreserving coord volume volume :=
  (volume_preserving_finTwoArrow (Fin 2 → ℝ)).trans
    ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ))

theorem coord_apply (h : Fin 2 → Fin 2 → ℝ) :
    coord h = ((h 0 0, h 0 1), (h 1 0, h 1 1)) := rfl

theorem complexMatrixMajorantIntegrable : Ad3.LR.C.ComplexMatrixMajorantIntegrable := by
  intro σ h0 h1
  refine ⟨6, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := by omega
  have hGi := integrable_Gi h0 h1
  have hsw : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Gi σ q.swap) := by
    have hmp : MeasurePreserving (Prod.swap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
        volume volume := Measure.measurePreserving_swap
    exact (hmp.integrable_comp hGi.aestronglyMeasurable).2 hGi
  have hsum := (hGi.add hsw).const_mul 2
  have hM : Integrable (fun h : Fin 2 → Fin 2 → ℝ =>
      2 * (Gi σ (coord h) + Gi σ (coord h).swap)) :=
    (coord_mp.integrable_comp hsum.aestronglyMeasurable).2 hsum
  refine hM.mono' ?_ (ae_of_all _ fun h => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  · have hxn : |h 0 0| ≤ ‖h‖ := (norm_le_pi_norm (h 0) 0).trans (norm_le_pi_norm h 0)
    have hpn : |h 0 1| ≤ ‖h‖ := (norm_le_pi_norm (h 0) 1).trans (norm_le_pi_norm h 0)
    have hyn : |h 1 0| ≤ ‖h‖ := (norm_le_pi_norm (h 1) 0).trans (norm_le_pi_norm h 1)
    have hun : |h 1 1| ≤ ‖h‖ := (norm_le_pi_norm (h 1) 1).trans (norm_le_pi_norm h 1)
    have hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
      simp [Matrix.det_fin_two]
    rw [hdet]
    have hn0 : 0 ≤ ‖h‖ := norm_nonneg _
    have hg1 := Gi_nonneg σ (coord h)
    have hg2 := Gi_nonneg σ (coord h).swap
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hD : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 0
    · rw [hD, abs_zero, Real.zero_rpow (by linarith)]
      simp only [zero_mul, zero_div]
      positivity
    by_cases hyx : |h 1 0| ≤ |h 0 0|
    · have hx : h 0 0 ≠ 0 := by
        intro hx
        have hy : h 1 0 = 0 := by
          rw [hx, abs_zero] at hyx
          exact abs_eq_zero.1 (le_antisymm hyx (abs_nonneg _))
        apply hD
        rw [hx, hy]
        ring
      have := core h0 h1 hN4 (u := h 1 1) hx hyx hxn hpn
      have hG : Gi σ (coord h) = G0 σ (h 0 0) (h 0 1) (h 1 0) (h 1 1) := by
        simp [Gi, coord_apply, hyx]
      rw [hG] at hg1 ⊢
      linarith
    · have hyx' : |h 0 0| ≤ |h 1 0| := (not_le.1 hyx).le
      have hy : h 1 0 ≠ 0 := by
        intro hy
        rw [hy, abs_zero] at hyx
        exact hyx (abs_nonneg _)
      have := core h0 h1 hN4 (p := h 1 1) (u := h 0 1) hy hyx' hyn hun
      have hG : Gi σ (coord h).swap = G0 σ (h 1 0) (h 1 1) (h 0 0) (h 0 1) := by
        simp [Gi, coord_apply, hyx']
      have e1 : |h 1 0 * h 0 1 - h 1 1 * h 0 0| = |h 0 0 * h 1 1 - h 0 1 * h 1 0| := by
        rw [abs_sub_comm]
        congr 1
        ring
      have e2 : h 1 0 ^ 2 + h 0 0 ^ 2 = h 0 0 ^ 2 + h 1 0 ^ 2 := add_comm _ _
      rw [e1, e2] at this
      rw [hG] at hg2 ⊢
      linarith

end GlobalTheory.CompanionTheory.TwoByTwoMajorant

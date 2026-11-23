import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetAreaLintegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal ComplexOrder

theorem gramVol_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

theorem enorm_mul_eq_ofReal_add {a r : ℝ} (hr : 0 ≤ r) :
    ‖a * r‖ₑ = ENNReal.ofReal a * ENNReal.ofReal r + ENNReal.ofReal (-a) * ENNReal.ofReal r := by
  rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, ← add_mul,
    ENNReal.ofReal_mul (abs_nonneg a)]
  congr 1
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos ha, ENNReal.ofReal_of_nonpos ha, zero_add]

section Abstract

variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_smul_mul_eq_toReal_sub {f : E → ℝ} (hf : Measurable f) (v : E) {ρ : ℂ → ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ)
    (hp : ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤)
    (hm : ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤) :
    ∫ t : ℂ, f (t • v) * ρ t =
      (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)).toReal -
        (∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)).toReal := by
  have hfv : Measurable fun t : ℂ => f (t • v) :=
    hf.comp (continuous_id.smul continuous_const).measurable
  have hint : Integrable (fun t : ℂ => f (t • v) * ρ t) := by
    refine ⟨(hfv.mul hρc.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ t : ℂ, ‖f (t • v) * ρ t‖ₑ
        = ∫⁻ t : ℂ, (ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) +
            ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)) :=
          lintegral_congr fun t => enorm_mul_eq_ofReal_add (hρ t)
      _ = (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)) +
            ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) :=
          lintegral_add_left ((ENNReal.measurable_ofReal.comp hfv).mul
            (ENNReal.measurable_ofReal.comp hρc.measurable)) _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hp.lt_top, hm.lt_top⟩
  have key : ∀ (a : ℝ) (t : ℂ), ENNReal.ofReal (a * ρ t) = ENNReal.ofReal a * ENNReal.ofReal (ρ t) :=
    fun a t => ENNReal.ofReal_mul' (hρ t)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  simp_rw [← neg_mul, key]

theorem finsum_integral_smul_mul_eq_toReal_sub {f : E → ℝ} (hf : Measurable f) {T : Set W}
    (hT : T.Finite) (v : W → E) (ρ : W → ℂ → ℝ) (hρ : ∀ w t, 0 ≤ ρ w t)
    (hρc : ∀ w, Continuous (ρ w))
    (hp : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤)
    (hm : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤) :
    ∑ᶠ w ∈ T, ∫ t : ℂ, f (t • v w) * ρ w t =
      (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal -
        (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hT] at hp hm ⊢
  have hp' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hp (Finset.single_le_sum (fun _ _ => zero_le) hw)
  have hm' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hm (Finset.single_le_sum (fun _ _ => zero_le) hw)
  rw [ENNReal.toReal_sum hp', ENNReal.toReal_sum hm', ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w hw =>
    integral_smul_mul_eq_toReal_sub hf (v w) (hρ w) (hρc w) (hp' w hw) (hm' w hw)

variable [MeasurableSpace X]

theorem mul_setIntegral_eq_of_lintegral_of_measurable {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hfm : Measurable f) (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨hGpm, hAp⟩ := hA (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
  obtain ⟨hGmm, hAm⟩ := hA (fun y => ENNReal.ofReal (-f y))
    (ENNReal.measurable_ofReal.comp hfm.neg)
  have hCp : ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.2).ne
  have hCm : ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.neg.2).ne
  have hIp : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCp
    rw [hAp] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hIm : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCm
    rw [hAm] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν] fun x =>
      (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) * ENNReal.ofReal (ρ x w t)).toReal -
        (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
          ENNReal.ofReal (ρ x w t)).toReal := by
    filter_upwards [ae_lt_top' hGpm hIp, ae_lt_top' hGmm hIm] with x hxp hxm
    exact finsum_integral_smul_mul_eq_toReal_sub hfm (hfin x) (v x) (ρ x) (hρ x) (hρc x)
      hxp.ne hxm.ne
  rw [integral_congr_ae hae, integral_sub (integrable_toReal_of_lintegral_ne_top hGpm hIp)
    (integrable_toReal_of_lintegral_ne_top hGmm hIm), integral_toReal hGpm (ae_lt_top' hGpm hIp),
    integral_toReal hGmm (ae_lt_top' hGmm hIm), integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    mul_sub, ← ENNReal.toReal_ofReal_mul c _ hc, ← ENNReal.toReal_ofReal_mul c _ hc, hAp, hAm,
    ENNReal.toReal_mul, ENNReal.toReal_mul, mul_sub]

theorem mul_setIntegral_eq_of_lintegral {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hf.1.ae_eq_mk)
  obtain ⟨hG0m, hA0⟩ := hA (N.indicator 1) (measurable_one.indicator hNm)
  rw [lintegral_indicator_one hNm, hN0, mul_zero, eq_comm, mul_eq_zero, or_iff_right hb,
    lintegral_eq_zero_iff' hG0m] at hA0
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν]
      fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, hf.1.mk f (t • v x w) * ρ x w t := by
    filter_upwards [hA0] with x hx
    refine finsum_mem_congr rfl fun w hw => integral_congr_ae ?_
    have hx' : ∫⁻ t : ℂ, N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) = 0 := by
      simp only [Pi.zero_apply, finsum_mem_eq_finite_toFinset_sum _ (hfin x),
        Finset.sum_eq_zero_iff] at hx
      exact hx w ((hfin x).mem_toFinset.2 hw)
    have hm : Measurable fun t : ℂ => N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) :=
      ((measurable_one.indicator hNm).comp (continuous_id.smul continuous_const).measurable).mul
        (ENNReal.measurable_ofReal.comp (hρc x w).measurable)
    rw [lintegral_eq_zero_iff' hm.aemeasurable] at hx'
    filter_upwards [hx'] with t ht
    rcases mul_eq_zero.1 ht with h | h
    · have hy : t • v x w ∉ N := by
        intro hy
        simp [Set.indicator_of_mem hy] at h
      have : f (t • v x w) = hf.1.mk f (t • v x w) := by
        by_contra hne
        exact hy (hsub hne)
      rw [this]
    · rw [ENNReal.ofReal_eq_zero] at h
      rw [le_antisymm h (hρ x w t), mul_zero, mul_zero]
  rw [integral_congr_ae hf.1.ae_eq_mk, integral_congr_ae hae]
  exact mul_setIntegral_eq_of_lintegral_of_measurable hfin v ρ hρ hρc hc hb hA
    hf.1.stronglyMeasurable_mk.measurable (hf.congr hf.1.ae_eq_mk)

end Abstract

theorem ConeSheetArea.proof (h : ConeSheetAreaLintegral.Statement) : ConeSheetArea.Statement := by
  intro n e S hS P Ψ f hP hΨ hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  exact mul_setIntegral_eq_of_lintegral
    (fun x => ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ x)
    (fun x w => WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩))
    (fun x w t => ‖t‖ ^ (2 * e) *
      gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)
    (fun x w t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ x))
    (fun x w => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => h n e S hS P Ψ F hP hΨ hF) hf

end GroundTheory.Heights₂.Heights

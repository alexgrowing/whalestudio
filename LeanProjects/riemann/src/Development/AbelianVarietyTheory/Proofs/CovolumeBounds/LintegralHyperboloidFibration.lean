import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConePolar

theorem angle_shift (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, h θ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), h θ := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

theorem radial (a : ℝ) (ha : 0 ≤ a) (F H : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Set.Ioi (Real.sqrt a), ENNReal.ofReal ρ * (F (ρ ^ 2 - a) * H ρ)
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * H (Real.sqrt (a + τ)) := by
  have himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0 := by
    ext τ
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have h0 := Real.sqrt_nonneg a
      have h1 := Real.sq_sqrt ha
      nlinarith
    · intro hτ
      refine ⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩
      rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a)) := by
    intro x hx y hy hxy
    have h0 := Real.sqrt_nonneg a
    simp only [Set.mem_Ioi] at hx hy
    have : x ^ 2 = y ^ 2 := by simpa using hxy
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
  have hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x)
      (Set.Ioi (Real.sqrt a)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))
    simpa using this
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj,
    ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (Real.sqrt_nonneg a).trans (le_of_lt hx)
  rw [show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]
  have : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1 := by
    rw [ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [this, one_mul]

theorem plane (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by
  rw [← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))),
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2) := by
    intro p
    rw [Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  have hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2 := by
    intro ρ θ
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z}
      (fun z => F (Complex.normSq z - a) * g z)) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
    exact (hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg
  simp only [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).mul (hm.comp ?_)
    fun_prop
  have hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ) := by
    rw [Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]
  rw [hsub, ← Measure.restrict_restrict measurableSet_Ioi,
    ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]
  split_ifs with h
  · have hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ)) :=
      hg.comp (by fun_prop)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]
    intro θ
    simp only
    congr 2
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]
  · simp

theorem measurable_snoc (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

theorem measurable_sqLen (k : ℕ) : Measurable (sqLen : (Fin k → ℂ) → ℝ) := by
  unfold sqLen
  exact Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)

theorem lintegral_snoc (k : ℕ) (f : (Fin (k + 1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v = ∫⁻ w : Fin k → ℂ, ∫⁻ z : ℂ, f (Fin.snoc (α := fun _ => ℂ) w z) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end GlobalTheory.HCXi.ConePolar

namespace GlobalTheory.HCXi
open ConePolar

theorem lintegral_cone_polar : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  intro k ψ F hψ hF
  have hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ) :=
    (measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)
  have hS := measurableSet_lt hinit hlast
  rw [← lintegral_indicator hS, lintegral_snoc k _
    (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]
  have h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator
      {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v)
      (Fin.snoc (α := fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ),
        F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w
          (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by
    intro w
    rw [← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F
      (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF
      (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]
    refine lintegral_congr fun z => ?_
    simp [Set.indicator]
  simp only [h1]
  have hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1.1
      (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ =>
      (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH := hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  rw [lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap
    (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]
  congr 1
  refine lintegral_congr fun τ => ?_
  have hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1
      (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ =>
      (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH' := hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  simp only at hH'
  rw [lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]

end GlobalTheory.HCXi

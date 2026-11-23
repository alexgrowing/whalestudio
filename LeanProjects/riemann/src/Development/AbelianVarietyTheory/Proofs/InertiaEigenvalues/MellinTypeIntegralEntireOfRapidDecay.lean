import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.MellinEntire

lemma min_inv_pos {t : ℝ} (ht : 0 < t) : 0 < min t t⁻¹ := lt_min ht (inv_pos.mpr ht)

lemma min_inv_le_one {t : ℝ} (ht : 0 < t) : min t t⁻¹ ≤ 1 := by
  rcases le_total t 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)

lemma le_inv_of_le_one' {t : ℝ} (ht : 0 < t) (h : t ≤ 1) : t ≤ t⁻¹ :=
  h.trans ((one_le_inv₀ ht).mpr h)

lemma inv_le_of_one_le' {t : ℝ} (h : 1 ≤ t) : t⁻¹ ≤ t :=
  (inv_le_one_of_one_le₀ h).trans h

lemma rpow_mul_min_pow_le {t σ : ℝ} {K : ℕ} (ht : 0 < t) (hσ : |σ| ≤ K) :
    t ^ σ * (min t t⁻¹) ^ K ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have h1 : t ^ σ ≤ t ^ (-(K:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [neg_abs_le σ])
    calc t ^ σ * t ^ K ≤ t ^ (-(K:ℝ)) * t ^ K := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have h1 : t ^ σ ≤ t ^ (K:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (le_trans (le_abs_self σ) hσ)
    calc t ^ σ * t⁻¹ ^ K ≤ t ^ (K:ℝ) * t⁻¹ ^ K := by gcongr
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]

lemma min_mul_abs_log_le {t : ℝ} (ht : 0 < t) : min t t⁻¹ * |Real.log t| ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have := Real.abs_log_mul_self_lt t ht h
    rw [abs_mul, abs_of_pos ht] at this
    linarith
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have := Real.abs_log_mul_self_lt t⁻¹ (inv_pos.mpr ht) (inv_le_one_of_one_le₀ h)
    rw [Real.log_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ht)] at this
    linarith

theorem integrable_and_differentiable {X : Type} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℂ) (T : X → ℝ)
    (hA : AEStronglyMeasurable A ν) (hT : Measurable T) (hTpos : ∀ x, 0 < T x)
    (hw : Integrable (fun x => min (T x) (T x)⁻¹) ν)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) :
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  have wpos : ∀ x, 0 < min (T x) (T x)⁻¹ := fun x => min_inv_pos (hTpos x)
  have wle : ∀ x, min (T x) (T x)⁻¹ ≤ 1 := fun x => min_inv_le_one (hTpos x)
  have hTc : Measurable fun x => ((T x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hT
  have meas : ∀ s : ℂ, AEStronglyMeasurable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν :=
    fun s => hA.mul (hTc.pow_const s).aestronglyMeasurable
  have bnd : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x (s : ℂ), |s.re| ≤ K →
      ‖A x * ((T x : ℝ) : ℂ) ^ s‖ ≤ C * (min (T x) (T x)⁻¹) ^ 2 := by
    intro K
    obtain ⟨C, hC⟩ := hdec (K + 2)
    refine ⟨|C|, abs_nonneg _, fun x s hs => ?_⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hTpos x)]
    have hA' : ‖A x‖ ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (wpos x).le _))
    have h2 := rpow_mul_min_pow_le (hTpos x) hs
    have h0 : 0 ≤ T x ^ s.re := Real.rpow_nonneg (hTpos x).le _
    calc ‖A x‖ * T x ^ s.re ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) * T x ^ s.re :=
          mul_le_mul_of_nonneg_right hA' h0
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 * (T x ^ s.re * (min (T x) (T x)⁻¹) ^ K) := by ring
      _ ≤ |C| * (min (T x) (T x)⁻¹) ^ 2 * 1 := by
          gcongr
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 := mul_one _
  have sq_le : ∀ x, (min (T x) (T x)⁻¹) ^ 2 ≤ min (T x) (T x)⁻¹ := fun x => by
    nlinarith [wpos x, wle x]
  refine ⟨fun s => ?_, fun s₀ => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := bnd ⌈|s.re|⌉₊
    refine Integrable.mono' (hw.const_mul C) (meas s) (ae_of_all _ fun x => ?_)
    exact (hC x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0)
  · obtain ⟨C, hC0, hC⟩ := bnd (⌈|s₀.re|⌉₊ + 1)
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ ((⌈|s₀.re|⌉₊ + 1 : ℕ) : ℝ) := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : |s.re| ≤ |s₀.re| + |s.re - s₀.re| := by
        have := abs_add_le s₀.re (s.re - s₀.re); simpa using this
      have h3 := Nat.le_ceil |s₀.re|
      push_cast
      linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s x => A x * ((T x : ℝ) : ℂ) ^ s)
      (F' := fun s x => A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ)))
      (x₀ := s₀) (bound := fun x => C * min (T x) (T x)⁻¹) (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => meas s) ((fun s => ?_ : ∀ s : ℂ,
        Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) s₀)
      (hA.mul ((hTc.pow_const s₀).mul (Complex.measurable_log.comp hTc)).aestronglyMeasurable)
      (ae_of_all _ fun x s hs => ?_) (hw.const_mul C)
      (ae_of_all _ fun x s _ => ?_)
    · exact key.2.differentiableAt
    · obtain ⟨C', hC0', hC'⟩ := bnd ⌈|s.re|⌉₊
      refine Integrable.mono' (hw.const_mul C') (meas s) (ae_of_all _ fun x => ?_)
      exact (hC' x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0')
    · show ‖A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ))‖ ≤ C * min (T x) (T x)⁻¹
      rw [← mul_assoc, norm_mul, ← Complex.ofReal_log (hTpos x).le, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := hC x s (hre s hs)
      have h2 := min_mul_abs_log_le (hTpos x)
      calc ‖A x * ((T x : ℝ) : ℂ) ^ s‖ * |Real.log (T x)|
          ≤ C * (min (T x) (T x)⁻¹) ^ 2 * |Real.log (T x)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = C * min (T x) (T x)⁻¹ * (min (T x) (T x)⁻¹ * |Real.log (T x)|) := by ring
        _ ≤ C * min (T x) (T x)⁻¹ * 1 := by
            gcongr
            exact mul_nonneg hC0 (wpos x).le
        _ = C * min (T x) (T x)⁻¹ := mul_one _
    · have hne : ((T x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hTpos x).ne'
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt.const_mul (A x)

end GlobalTheory.MellinEntire

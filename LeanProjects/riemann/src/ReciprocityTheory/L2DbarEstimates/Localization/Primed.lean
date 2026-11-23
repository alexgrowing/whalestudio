import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem primed_lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a F G : α → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : ∀ x, a x ^ 2 ≤ F x * G x) :
    (∫⁻ x, a x ∂μ) ^ 2 ≤ (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
  have hpt : ∀ x, a x ≤ F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := by
    intro x
    calc a x = (a x ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (F x * G x) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (h x) (by norm_num)
      _ = F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hF.pow_const (1 / 2 : ℝ)) (hG.pow_const (1 / 2 : ℝ))
  have hsq : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = y := by
    intro y; rw [← ENNReal.rpow_mul]; norm_num
  simp only [hsq, Pi.mul_apply] at hH
  have hle : ∫⁻ x, a x ∂μ ≤ (∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ) :=
    (lintegral_mono hpt).trans hH
  calc (∫⁻ x, a x ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

theorem primed_ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable hm]
    simp

theorem primed_inner_norm (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by
  have : ⟪dbarF n z F0 x, g x⟫_ℂ = starRingEnd ℂ (dbarDot n z F0 x (fun j => g x j)) := by
    simp [dbarF, dbarDot, PiLp.inner_apply, map_sum, mul_comm]
  rw [this, Complex.norm_conj]

theorem primedIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hAP : APStatement n M) : PrimedIneqStatement n M := by
  intro z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hpp hlevi hA g hg
  have cR : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf => by
    exact (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have cph' := cR ph' hph'
  have cψ := cR ψ hψ
  have cg : ∀ j, Continuous fun x => g x j := fun j => Ck.continuous n z hz 2 _ (hg j).1
  have cLevi : ∀ q : M → ℝ, SmoothR n z q →
      Continuous fun x => (Levi n z q x (fun j => g x j)).re := by
    intro q hq
    refine Complex.continuous_re.comp ?_
    unfold Levi
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact ((Smooth.continuous n z hz _ (Smooth.d n z j _ (Smooth.db n z k _ hq))).mul
      (cg j)).mul (Complex.continuous_conj.comp (cg k))
  have cdS : Continuous fun x => dSqR n z ψ x := by
    unfold dSqR
    exact continuous_finsetSum _ fun j _ =>
      ((Smooth.continuous n z hz _ (Smooth.d n z j _ hψ)).norm.pow 2)
  have hnorm : ∀ x, ‖g x‖ ^ 2 = ∑ j, ‖g x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (g x)
  have cgn : Continuous fun x => ‖g x‖ ^ 2 := by
    simp_rw [hnorm]; exact continuous_finsetSum _ fun j _ => (cg j).norm.pow 2
  have hKc : IsCompact (⋃ j, tsupport (fun x => g x j)) :=
    isCompact_iUnion fun j => (hg j).2
  have hgK : ∀ x, x ∉ (⋃ j, tsupport (fun x => g x j)) → g x = 0 := by
    intro x hx
    simp only [mem_iUnion, not_exists] at hx
    ext j
    exact image_eq_zero_of_notMem_tsupport (f := fun x => g x j) (hx j)
  set Q : M → ℝ := fun x => ((Levi n z ph' x (fun j => g x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖g x‖ ^ 2) * Real.exp (-ph' x) with hQ
  have cQ : Continuous Q := ((cLevi ph' hph').sub ((continuous_const.mul cdS).mul cgn)).mul
    (Real.continuous_exp.comp cph'.neg)
  have sQ : HasCompactSupport Q := HasCompactSupport.intro hKc fun x hx => by
    simp [hQ, hgK x hx, Levi]
  have iQ : Integrable Q (vol n z) := integrable_of_continuous_real n z hz Q cQ sQ
  have hL0 : ∀ x, 0 ≤ (Levi n z ph x (fun j => g x j)).re := fun x => hlev x _
  have hLQ : ∀ x, (Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x) ≤ Q x := by
    intro x
    have h1 := hlevi x (fun j => g x j)
    beta_reduce at h1
    rw [← hnorm x] at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    (mul_nonneg (hL0 x) (Real.exp_pos _).le).trans (hLQ x)
  have hap := hAP z hz ph' ψ ε g (SmoothR.ckR n z 2 ph' hph') (SmoothR.ckR n z 1 ψ hψ) hε hg
  set Gf : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x)) with hGf
  set Ff : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) with hFf
  have hG : ∫⁻ x, Gf x ∂vol n z ≤ ENNReal.ofReal (1 + ε) *
      wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) g) (w1 ph' ψ) + n2 n z (sbar n z g) ph' := by
    calc ∫⁻ x, Gf x ∂vol n z ≤ ∫⁻ x, ENNReal.ofReal (Q x) ∂vol n z :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hLQ x)
      _ = ENNReal.ofReal (∫ x, Q x ∂vol n z) :=
          (ofReal_integral_eq_lintegral_ofReal iQ (Eventually.of_forall hQ0)).symm
      _ ≤ ENNReal.ofReal ((1 + ε) * (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) :=
          ENNReal.ofReal_le_ofReal hap
      _ ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ENNReal.ofReal (∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) := by
          rw [← ENNReal.ofReal_mul (by linarith)]; exact ENNReal.ofReal_add_le
      _ ≤ _ := by
          gcongr
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le
  have hF : ∫⁻ x, Ff x ∂vol n z ≤ ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z :=
    lintegral_mono fun x => by
      simp only [hFf]
      gcongr
      linarith [hpp x]
  have mF : AEMeasurable Ff (vol n z) :=
    (hh.mul (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul cψ).sub cph')).measurable)).aemeasurable
  have mG : AEMeasurable Gf (vol n z) :=
    (ENNReal.continuous_ofReal.comp ((cLevi ph hph).mul
      (Real.continuous_exp.comp cph'.neg))).measurable.aemeasurable
  set I : M → ℂ := fun x => ⟪dbarF n z F0 x, g x⟫_ℂ * (Real.exp (-w2 ph' ψ x) : ℂ) with hI
  have hpt : ∀ x, ‖I x‖ₑ ^ 2 ≤ Ff x * Gf x := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [hI, hFf, hGf]
    rw [norm_mul, primed_inner_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow]
    have he : Real.exp (-w2 ph' ψ x) ^ 2 = Real.exp (2 * ψ x - ph' x) * Real.exp (-ph' x) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; simp only [w2]; ring
    rw [he, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (hL0 x)]
    calc ENNReal.ofReal (‖dbarDot n z F0 x (fun j => g x j)‖ ^ 2) *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x)))
        ≤ h x * ENNReal.ofReal (Levi n z ph x (fun j => g x j)).re *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x))) := by
          gcongr; exact hdom x _
      _ = _ := by ring
  show ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) ≤ _
  calc ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) = ‖∫ x, I x ∂vol n z‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ (∫⁻ x, ‖I x‖ₑ ∂vol n z) ^ 2 := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ ≤ (∫⁻ x, Ff x ∂vol n z) * ∫⁻ x, Gf x ∂vol n z :=
        primed_lintegral_sq_le _ _ _ _ mF mG hpt
    _ ≤ _ := mul_le_mul' hF hG

end

end ReciprocityTheory.L2DbarEstimates.F

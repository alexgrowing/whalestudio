import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem real_smul_mem_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) (t : ℝ) :
    t • y ∈ coneSet h J := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  intro q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy (t : ℂ) q hq

theorem coneFibreAverage_of_lt {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      1 * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * m)
  rw [Real.hausdorffMeasure_of_finrank_lt hlt, Measure.coe_zero, Pi.zero_apply, mul_zero]
  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) = 0 := by
    intro π
    rw [lintegral_congr_ae (g := fun _ => 0) (ae_restrict_of_ae (by
        filter_upwards [ae_fibreCount_eq_zero hnm h J π] with w hw
        simp [hw])), lintegral_zero]
  simp [hin]

theorem coneFibreAverage_zero {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w ≠ ⊤) :
    ∫⁻ π : Fin 0 → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1, (fibreCount h J π w : ℝ≥0∞) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1) *
        Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  have hcount : ∀ (π : Fin 0 → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin 0)),
      fibreCount h J π w = (coneSet h J).encard := by
    intro π w
    rw [fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  obtain ⟨π₀, hπ₀⟩ := hfib.exists
  obtain ⟨w₀, hw₀⟩ := hπ₀.exists
  rw [hcount] at hw₀
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      rw [HermNorm.pointOf_smul']
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    exact hw₀ (hinf.mono hsub').encard_eq
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} = coneSet h J := by
    ext y
    refine ⟨fun hy => hy.2, fun hy => ⟨?_, hy⟩⟩
    rw [Set.mem_singleton_iff.1 (hsub hy)]
    simp
  have hmass : Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ) (coneSet h J) =
      ((coneSet h J).encard : ℝ≥0∞) := by
    rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
    · rw [h0]
      simp
    · rw [h0, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton,
        Set.encard_singleton]
      simp
  have hgauss : ∀ π : Fin 0 → Fin n → ℂ, matGauss π = 1 := by
    intro π
    simp [matGauss]
  have huniv : (volume : Measure (Fin 0 → Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp_rw [hgauss, hcount, one_mul, setLIntegral_const]
  rw [lintegral_const, huniv, mul_one, hset, hmass, mul_comm]

theorem ConeFibreAverage.proof (hA : ConeAreaFormula.Statement) (hT : ConeTangentAverage.Statement)
    (hR : ConeRadialIntegral.Statement) (hG : TangentGaussMoment.Statement) :
    ConeFibreAverage.Statement := by
  intro n m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1), Metric.measure_ball_pos _ _ one_pos,
      measure_ball_lt_top, fun h J hJ hfib => coneFibreAverage_zero h J hJ hfib⟩
  by_cases hmn : m ≤ n
  swap
  · exact ⟨1, one_pos, ENNReal.one_lt_top, fun h J _ _ => coneFibreAverage_of_lt (by omega) h J⟩
  obtain ⟨hkm, hkanti, hkpos, hM0, hMtop⟩ := hG n m hm hmn
  set μ := Measure.hausdorffMeasure (X := EuclideanSpace ℂ (Fin n)) ((2 * m : ℕ) : ℝ) with hμ
  set k := tangentGaussProfile n m with hk
  set M := ∫⁻ r in Set.Ioi (0 : ℝ), k r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hM
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨H, hHdef⟩ : ∃ H, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = H := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = V := ⟨_, rfl⟩
  have hH0 : H ≠ 0 := by
    rw [← hHdef, hd]
    exact (Metric.measure_ball_pos _ _ one_pos).ne'
  have hHtop : H ≠ ⊤ := by
    rw [← hHdef, hd]
    exact measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := hVdef ▸ (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ⊤ := hVdef ▸ measure_ball_lt_top.ne
  have hc0 : H⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hHtop) hV0
  have hctop : H⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hH0) hVtop
  refine ⟨H⁻¹ * V * M, ENNReal.mul_pos hc0 hM0.ne', ENNReal.mul_lt_top hctop.lt_top hMtop, ?_⟩
  intro h J hJ hfib

  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
        H⁻¹ * V * ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y) ∂μ := by
    intro π
    have harea := hA n m h J hJ hm hmn hfib π ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet)
    have hind : ∫⁻ w, (fibreCount h J π w : ℝ≥0∞) * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 w = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
      congr 1
      funext w
      by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1 <;> simp [hw]
    rw [hind, hVdef, hHdef] at harea
    rw [mul_assoc, harea, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHtop, one_mul]
  have hlhs : ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      H⁻¹ * V * ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
    rw [← hT n m h J hJ hm hmn hfib, ← lintegral_const_mul' _ _ hctop]
    refine lintegral_congr fun π => ?_
    rw [hin π]
    ring
  rw [hlhs]
  by_cases hfin : μ {y | ‖y‖ < 1 ∧ y ∈ coneSet h J} < ⊤
  · rw [hR n m hm (coneSet h J) (fun y hy t _ => real_smul_mem_coneSet h hJ hy t) hfin k hkm]
    ring
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, ENNReal.mul_top (ENNReal.mul_pos hc0 hM0.ne').ne']
    have hball : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} :=
      measurableSet_lt measurable_norm measurable_const
    have hge : k 1 * ⊤ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
      calc k 1 * ⊤ = ∫⁻ y in coneSet h J, {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1}.indicator
              (fun _ => k 1) y ∂μ := by
            rw [lintegral_indicator_const hball, Measure.restrict_apply hball]
            congr 1
            exact hfin.symm
        _ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
            refine lintegral_mono fun y => ?_
            by_cases hy : ‖y‖ < 1
            · rw [Set.indicator_of_mem (show y ∈ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact hkanti (Set.mem_Ici.2 (norm_nonneg y)) (Set.mem_Ici.2 zero_le_one) hy.le
            · rw [Set.indicator_of_notMem (show y ∉ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact bot_le
    rw [ENNReal.mul_top (hkpos 1).ne', top_le_iff] at hge
    rw [hge, ENNReal.mul_top hc0]

end

end GroundTheory.Heights₂.Heights

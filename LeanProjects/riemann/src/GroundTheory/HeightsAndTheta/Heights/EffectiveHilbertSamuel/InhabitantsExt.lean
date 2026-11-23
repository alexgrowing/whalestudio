import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCompact
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtNonInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace ExtInhabitants

def c0 : Fin (flatAtlas 1).n := ⟨0, Nat.one_pos⟩

theorem piece_flat : piece (flatAtlas 1) c0 = univ := by
  ext y
  simp only [piece, mem_ofPred_eq, mem_univ, iff_true]
  exact ⟨by simp, fun k hk => absurd hk (by simp [c0, Fin.lt_def])⟩

theorem chartIntegral_flat (f : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℝ≥0∞) :
    chartIntegral (flatAtlas 1) f = ∫⁻ y, f c0 y := by
  unfold chartIntegral
  rw [Fintype.sum_subsingleton _ c0, piece_flat, Measure.restrict_univ]
  simp

theorem exp_neg_wt (m : ℕ) (y : Fin 1 → ℂ) :
    Real.exp (-exEmb.wt m c0 y) = ((1 + ‖y 0‖ ^ 2) ^ m)⁻¹ := by
  have he : ∑ k : Fin 2, ‖exE k c0 y‖ ^ 2 = 1 + ‖y 0‖ ^ 2 := by
    simp [exE, Fin.sum_univ_two]
  have he₂ : ∑ k : Fin 1, ‖exE₂ k c0 y‖ ^ 2 = 1 := by simp [exE₂]
  simp only [EmbDatum.wt, fsWeight]
  change Real.exp (-(Real.log (∑ k : Fin 1, ‖exE₂ k c0 y‖ ^ 2) +
    (m : ℝ) * Real.log (∑ k : Fin 2, ‖exE k c0 y‖ ^ 2))) = _
  rw [he, he₂, Real.log_one, zero_add, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (by positivity)]

theorem one_add_pow_three_le (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 3 ≤ 4 * (1 + t ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t ^ 2 - t), sq_nonneg t, mul_nonneg ht (sq_nonneg t),
    mul_nonneg ht (sq_nonneg (t - 1))]

theorem lintegral_inv_one_add_sq_sq_lt_top (c : ℝ) :
    ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹) < ⊤ := by
  have hfin : (Module.finrank ℝ (Fin 1 → ℂ) : ℝ) < 3 := by
    rw [Module.finrank_pi_fintype]; simp; norm_num
  have hI := finite_integral_one_add_norm (E := Fin 1 → ℂ) (μ := volume) hfin
  have hpt : ∀ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹) ≤
      ENNReal.ofReal (4 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hy : ‖y‖ ≤ ‖y 0‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [Subsingleton.elim i 0]
    have hr : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [hr]
    have he : ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖y 0‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith [one_add_pow_three_le ‖y 0‖ (norm_nonneg _)]
    have hmono : ((1 + ‖y 0‖) ^ 3)⁻¹ ≤ ((1 + ‖y‖) ^ 3)⁻¹ := by
      apply inv_anti₀ (by positivity)
      gcongr
    calc c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ ≤ |c| * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ := by
          gcongr; exact le_abs_self c
      _ ≤ |c| * (4 * ((1 + ‖y 0‖) ^ 3)⁻¹) := by gcongr
      _ ≤ |c| * (4 * ((1 + ‖y‖) ^ 3)⁻¹) := by gcongr
      _ = 4 * |c| * ((1 + ‖y‖) ^ 3)⁻¹ := by ring
  calc ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹)
      ≤ ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (4 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (4 * |c|) * ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

def exZdz : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ y => y 0

end ExtInhabitants

open ExtInhabitants

theorem extDelta_hyp : ∃ (X : EmbDatum 1) (Z : ZeroDatum X), 1 ≤ 1 ∧ 2 ≤ 2 ∧ Z.S.Nonempty :=
  ⟨exEmb, exZ, le_rfl, le_rfl, ⟨0, by
    change (0 : Fin 1 → ℂ) ∈ zeroSet (flatAtlas 1) (fun i => lin exE (exC i))
    rw [exZero]; rfl⟩⟩

theorem topSecCompact_hyp : ∃ (F : ℕ → Fin exEmb.A.n → exEmb.U → ℂ) (C : ℝ),
    (∀ n, F n ∈ topSections exEmb.A exEmb.L₂ exEmb.L 2) ∧
    (∀ n, topNormSq exEmb.A (exEmb.wt 2) (F n) ≤ ENNReal.ofReal C) ∧ F 0 ≠ 0 := by
  have hfin : topNormSq exEmb.A (exEmb.wt 2) exOne < ⊤ := by
    change chartIntegral (flatAtlas 1) _ < ⊤
    rw [chartIntegral_flat]
    simp only [exOne, norm_one, one_pow, mul_one]
    simp only [exp_neg_wt]
    simpa using lintegral_inv_one_add_sq_sq_lt_top 2
  refine ⟨fun _ => exOne, (topNormSq exEmb.A (exEmb.wt 2) exOne).toReal,
    fun _ => mem_topSections_flat 2 (fun _ => 1) analyticOnNhd_const,
    fun _ => (ENNReal.ofReal_toReal hfin.ne).ge, fun h => ?_⟩
  have := congr_fun (congr_fun h c0) 0
  simp [exOne] at this

theorem extNonInt_hyp :
    (∀ k, ContinuousOn (exZdz k ∘ (exEmb.A.chart k).symm) (exEmb.A.chart k).target) ∧
    (∀ k l, ∀ x ∈ (exEmb.A.chart k).source ∩ (exEmb.A.chart l).source,
      exZdz k x = jac exEmb.A k l x * exEmb.L₂.g k l x * exEmb.L.g k l x ^ 3 * exZdz l x) ∧
    chartIntegral exEmb.A (fun k y => ENNReal.ofReal (2 ^ 1 * ‖exZdz k y‖ ^ 2 *
      Real.exp (-exEmb.wt 3 k y) * extFactor 1 1 0 (extEv exZ k y))) < ⊤ ∧ exZdz ≠ 0 := by
  refine ⟨fun k => ?_, fun k l x _ => by simp [exZdz, jac_flat, trivLB], ?_, fun h => ?_⟩
  · exact (continuous_apply 0).continuousOn
  · change chartIntegral (flatAtlas 1) _ < ⊤
    rw [chartIntegral_flat]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lintegral_inv_one_add_sq_sq_lt_top 2)
    apply ENNReal.ofReal_le_ofReal
    have hev : extEv exZ c0 y = ‖y 0‖ ^ 2 * (1 + ‖y 0‖ ^ 2)⁻¹ := by
      have hs : ∑ i : Fin 1, ‖exZ.s i c0 y‖ ^ 2 = ‖y 0‖ ^ 2 := by
        simp [ZeroDatum.s, exS_apply]
      have he : fsWeight exE c0 y = Real.log (1 + ‖y 0‖ ^ 2) := by
        simp [fsWeight, exE, Fin.sum_univ_two]
      have hr : rSq exZ.c = 1 := by
        simp [rSq, exC, Fin.sum_univ_two]
      unfold extEv
      rw [hs, he, hr, Real.exp_neg, Real.exp_log (by positivity), div_one]
    have hw : Real.exp (-exEmb.wt 3 c0 y) = ((1 + ‖y 0‖ ^ 2) ^ 3)⁻¹ := exp_neg_wt 3 y
    have ha0 : 0 ≤ ‖y 0‖ ^ 2 := by positivity
    simp only [exZdz, hw, hev]
    unfold extFactor
    rw [zero_pow two_ne_zero, add_zero, pow_one]
    generalize ‖y 0‖ ^ 2 = a at ha0 ⊢
    rcases ha0.lt_or_eq with hapos | ha0'
    · have hden : 1 ≤ extDen 1 (a * (1 + a)⁻¹) := by
        have ht1 : a * (1 + a)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
        have hx : 1 ≤ extX 1 (a * (1 + a)⁻¹) := by
          unfold extX
          have : Real.log (a * (1 + a)⁻¹ + 1 ^ 2) ≤ Real.log (1 + 1 ^ 2) :=
            Real.log_le_log (by positivity) (by linarith)
          linarith
        unfold extDen curvEta
        have := Real.log_nonneg hx
        nlinarith
      have hne : (1 + a) ≠ 0 := by positivity
      calc _ = 2 * ((1 + a) ^ 2)⁻¹ / extDen 1 (a * (1 + a)⁻¹) := by field_simp
        _ ≤ _ := div_le_self (by positivity) hden
    · rw [← ha0']
      simp
  · have := congr_fun (congr_fun h c0) (fun _ => 1)
    simp [exZdz] at this

end

end GroundTheory.Heights₂.Heights.EffectiveHS

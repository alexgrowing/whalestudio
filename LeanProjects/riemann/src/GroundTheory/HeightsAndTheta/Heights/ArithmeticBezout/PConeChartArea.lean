import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem integral_indicator_ball_norm_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  have hfun : (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) =
      fun t => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) ‖t‖ := by
    ext t
    simp [Set.indicator]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) r)]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y = R ^ (2 * e + 2) / (2 * e + 2) := by
    have hpt : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y) =
        (Iio R).indicator (fun y : ℝ => y ^ (2 * e + 1)) := by
      ext y
      by_cases hy : y < R
      · simp [Set.indicator, hy, Complex.finrank_real_complex, pow_succ]
        ring
      · simp [Set.indicator, hy]
    rw [hpt, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
    push_cast
    ring_nf
  rw [hint, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem le_of_isArithVar_pblk {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    d ≤ n := by
  have h := ringKrullDim_quotient_le P
  rw [hP.2.2.2, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
  have hc : Nat.card (Σ k : Unit, PBlk n k) = n := by
    simp [Nat.card_eq_fintype_card]
  rw [hc, Fintype.card_unit] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + n : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h
  have h'' : d + 1 ≤ 1 + n := by exact_mod_cast h'
  omega

theorem integral_chosenSheet_eq {n e : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (g : (Fin n → ℂ) → ℝ) (hg : ∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z)
    (x : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * chartGramDensity P Ψ S g x w := by
  classical
  by_cases hγ : ∃ γ, IsSheet P Ψ x w γ
  · have hc : chosenSheet P Ψ x w = hγ.choose := by
      simp only [chosenSheet, dif_pos hγ]
    have hd : chartGramDensity P Ψ S g x w = g (fun i => hγ.choose x ⟨(), i⟩) *
        ((e.factorial : ℝ) / Real.pi ^ e *
            gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x /
          ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose x ⟨(), i⟩)‖ ^ (2 * (e + 1))) := by
      simp only [chartGramDensity, dif_pos hγ]
    rw [hc, hd]
    set u : Fin n → ℂ := fun i => hγ.choose x ⟨(), i⟩ with hu_def
    set G := gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x with hG_def
    have hmem : hγ.choose x ∈ mcPts P := (hγ.choose_spec.2.self_of_nhds).2.1
    have hu : u ≠ 0 := by
      obtain ⟨i, hi⟩ := hmem.1 ()
      intro h
      exact hi (congrFun h i)
    have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
    have hinv : S⁻¹ *ᵥ (S *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hdet, Matrix.one_mulVec]
    have hSu : S *ᵥ u ≠ 0 := by
      intro h
      apply hu
      rw [← hinv, h, Matrix.mulVec_zero]
    set ρ := ‖WithLp.toLp 2 (S *ᵥ u)‖ with hρ_def
    have hρ : 0 < ρ := by
      rw [hρ_def, norm_pos_iff]
      intro h
      exact hSu (by simpa using congrArg WithLp.ofLp h)
    have hpt : ∀ t : ℂ, (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ u)) =
        t • u := by
      intro t
      have : (fun i => (t • WithLp.toLp 2 (S *ᵥ u)) i) = t • (S *ᵥ u) := by
        ext i
        simp
      simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose, this,
        Matrix.mulVec_smul, hinv]
    have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ u)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
        fun t => (g u * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [h0] with t ht
      have hiff : ‖t • WithLp.toLp 2 (S *ᵥ u)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
        rw [norm_smul, lt_div_iff₀ hρ]
      by_cases hb : ‖t‖ < 1 / ρ
      · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
          indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t u ht]
        ring
      · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
          indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
        ring
    rw [integral_congr_ae hae, integral_const_mul,
      integral_indicator_ball_norm_pow e (by positivity)]
    rw [one_div, inv_pow, Nat.factorial_succ]
    have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hc : chosenSheet P Ψ x w = 0 := by
      simp only [chosenSheet, dif_neg hγ]
    have hd : chartGramDensity P Ψ S g x w = 0 := by
      simp only [chartGramDensity, dif_neg hγ]
    have hG : gramVol (fun x' => S *ᵥ fun i =>
        (0 : (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ) x' ⟨(), i⟩) x = 0 := by
      have hz : (S *ᵥ fun _ : Fin n => (0 : ℂ)) = 0 := Matrix.mulVec_zero S
      have hw : ∀ a : Fin (e + 1), (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) :
          Fin (e + 1) → Fin n → ℂ) a = 0 := fun a => Fin.cases rfl (fun _ => rfl) a
      simp [gramVol, hz, hw]
      rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 from rfl,
        Matrix.det_zero, Complex.zero_re]
    rw [hc, hd, hG]
    simp

theorem ConeChartArea.proof (hA : ConeSheetArea.Statement) : ConeChartArea.Statement := by
  intro n e S hS P Ψ g hP hΨ _hgm hdeg hint
  set C := coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) with hC
  set f : EuclideanSpace ℂ (Fin n) → ℝ := (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
    (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)) with hf
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
      eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0} = C ∩ ball 0 1 := by
    ext y
    simp only [hC, coneSet, mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
    exact and_comm
  have hfC : IntegrableOn f C (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn,
      Measure.restrict_restrict measurableSet_ball, inter_comm]
    rw [hset] at hint
    exact hint
  have key := hA n e S hS P Ψ f hP hΨ hfC
  have hterm : ∀ x : Fin e → ℂ, (∑ᶠ w ∈ fibre P Ψ x, ∫ t : ℂ,
      f (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        ∑ᶠ w ∈ fibre P Ψ x, chartGramDensity P Ψ S g x w := by
    intro x
    rw [mul_finsum_mem]
    exact finsum_mem_congr rfl fun w _ => integral_chosenSheet_eq S hS P Ψ g hdeg x w
  simp_rw [hterm, integral_const_mul] at key
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  have hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal :=
    ENNReal.toReal_pos hM0.ne' hMtop.ne
  have hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) := by positivity
  have hleft : ∫ y in C, f y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫ y in {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
        eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0},
        g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)
          ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [hf, setIntegral_indicator measurableSet_ball, hset]
  rw [hleft] at key
  unfold coneIntegral
  rw [div_eq_iff hM.ne']
  have key' := key
  rw [mul_left_comm] at key'
  have := mul_left_cancel₀ hc.ne' key'
  rw [this, mul_comm]

end GroundTheory.Heights₂.Heights

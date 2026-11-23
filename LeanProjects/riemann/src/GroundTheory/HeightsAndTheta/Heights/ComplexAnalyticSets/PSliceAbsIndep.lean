import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceAbsIndep
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConePolar
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

open scoped ENNReal

noncomputable section

theorem finsum_const_mul_ofReal {α : Type*} (c : ℝ≥0∞) (hc : c ≠ 0) (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ᶠ x, c * ENNReal.ofReal (g x) = c * ENNReal.ofReal (∑ᶠ x, g x) := by
  have hsupp : (Function.support fun x => c * ENNReal.ofReal (g x)) = Function.support g := by
    ext x
    simp only [Function.mem_support, ne_eq, mul_eq_zero, hc, false_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hg x) (Ne.symm h)⟩
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [hsupp]),
      ← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => hg i]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hsupp]),
      ENNReal.ofReal_zero, mul_zero]

theorem gramVol_zero_map {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  have hw : (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    ext a i
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have hM0 : (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 := rfl
  simp [gramVol, hw, hM0, Matrix.det_zero]

theorem lintegral_line_gram_abs {n : ℕ} (e : ℕ) (h : HermNorm n) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ)
    (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (|w x| * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1))))) := by
  have hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => |w x|) (t • x) = (fun x => |w x|) x :=
    fun t x ht => by simp only [hw t x ht]
  have key := integral_line_gram e h (fun x => |w x|) hg x hx G
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    apply hx
    rw [← hinv, show (h.matᵀ)⁻¹ *ᵥ x = 0 by simpa using congrArg WithLp.ofLp h0, Matrix.mulVec_zero]
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (|w x| * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hw t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  have hint : Integrable (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) := by
    refine (((integrable_indicator_iff measurableSet_ball).2 ?_).const_mul (|w x| * G)).congr hae.symm
    exact ((continuous_norm.pow _).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (1 / ρ))).mono_set ball_subset_closedBall
  have hfun : (fun t : ℂ => ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) = fun t => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) :=
    funext fun t => (ENNReal.ofReal_mul (indicator_nonneg (fun _ _ => abs_nonneg _) _)).symm
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _) (by positivity))]
  exact congrArg ENNReal.ofReal key

theorem sheetSum_lintegral_eq {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (y : Fin (e + 1) → ℂ) :
    (∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
        (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
      ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
    ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
      ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
        (fun _ x => Real.log (h.dualNorm x)) y) := by
  have hc : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold chartAbsDens sheetSum
  rw [finsum_mem_def, finsum_mem_def, ← finsum_const_mul_ofReal _ hc _
    (fun x => indicator_nonneg (fun x _ => by dsimp only; split_ifs; exacts [abs_nonneg _, le_rfl]) x)]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    by_cases hs : ∃ s, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = hs.choose := by
        unfold sheetThrough; rw [dif_pos hs]
      obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      have hG := gramVol_nonneg (fun y' => (h.matᵀ)⁻¹ *ᵥ hs.choose y') y
      have hd : 0 ≤ h.dualNorm x ^ (2 * (e + 1 + 1)) :=
        pow_nonneg (by unfold HermNorm.dualNorm; positivity) _
      have hm := maDens_log_dualNorm_sheet h J ℓ A y x hs.choose hx hs.choose_spec
      beta_reduce at hm
      rw [dif_pos hs, hsT, hy, lintegral_line_gram_abs (e + 1) h w hw x hx0 _ hG]
      beta_reduce
      rw [hm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) hG) hd),
        ← ENNReal.ofReal_mul (by positivity)]
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = 0 := by
        unfold sheetThrough; rw [dif_neg hs]
      rw [dif_neg hs, hsT]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, gramVol_zero_map, mul_zero, ENNReal.ofReal_zero,
        lintegral_zero]
  · simp [indicator_of_notMem hx]

theorem SliceAbsIndep.proof (hL : ConeSheetGramLintegral.Statement) (hD : ConeDimOfChowForm.Statement) :
    SliceAbsIndep.Statement := by
  intro n e h J F ℓ ℓ' A A' w hJ hF hℓ hℓ' hA hA' hwm hw
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) :=
    hD ℂ n (e + 2) J F hJ hF
  have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
    unfold HermNorm.pointOf
    exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
  have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
      ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|) z) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (hwm.comp hpm.measurable)).indicator measurableSet_ball)
  have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hR : ∀ (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
      (∫⁻ y, ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
        ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
        ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
      ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
        ∫⁻ y, ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
          (fun _ x => Real.log (h.dualNorm x)) y) := fun ℓ A => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun y => sheetSum_lintegral_eq h J ℓ A w hw y
  have k1 := (hL n (e + 1) h J ℓ A _ hJ hdim hℓ hA hFm).2
  have k2 := (hL n (e + 1) h J ℓ' A' _ hJ hdim hℓ' hA' hFm).2
  rw [hR] at k1 k2
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1 + 1) (le_of_ringKrullDim_quotient J hdim)
  have key := k1.symm.trans k2
  rwa [ENNReal.mul_right_inj hM0.ne' hMtop.ne, ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top] at key

end

end GroundTheory.Heights₂.Heights

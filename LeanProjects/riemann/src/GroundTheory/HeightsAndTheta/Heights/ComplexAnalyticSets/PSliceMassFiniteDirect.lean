import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceAbsIndep
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

theorem SliceMassFinite.proof' (hL : ConeSheetGramLintegral.Statement) (hMF : MassFinite.Statement)
    (hD : ConeDimOfChowForm.Statement) : SliceMassFinite.Statement := by
  intro n d h I ℓ A hI hℓ hdim hA
  cases d with
  | zero =>
    have hconst : chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) =
        fun _ => chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) 0 :=
      funext fun y => congrArg _ (Subsingleton.elim y 0)
    rw [hconst]
    have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
      infer_instance
    exact integrable_const _
  | succ e =>
    obtain ⟨W, F, hW, hFW, hℓW, hWI⟩ := SliceMassFinite.exists_projClosure I ℓ hI hℓ hdim
    subst hWI
    have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) :=
      hD ℂ n (e + 2) W F hW hFW
    have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
      unfold HermNorm.pointOf
      exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
    have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z) :=
      ENNReal.measurable_ofReal.comp (measurable_const.indicator measurableSet_ball)
    have k1 := (hL n (e + 1) h W ℓ A _ hW hdimW hℓW hA hFm).2
    rw [lintegral_congr fun y => sheetSum_lintegral_eq h W ℓ A (fun _ => (1 : ℝ))
      (fun _ _ _ => rfl) y, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at k1

    have hball : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf z) q = 0},
        ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z)
          ∂(Measure.hausdorffMeasure ((2 * (e + 1 + 1) : ℕ) : ℝ)) < ⊤ := by
      have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
          ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
            (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z)) =
          (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator 1 := by
        funext z
        by_cases hz : z ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 1
        · simp [indicator_of_mem hz]
        · simp [indicator_of_notMem hz]
      rw [hfun, lintegral_indicator_one measurableSet_ball, Measure.restrict_apply measurableSet_ball]
      have hset : ball (0 : EuclideanSpace ℂ (Fin n)) 1 ∩
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf z) q = 0} =
          {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf z) q = 0} := by
        ext z
        simp
      rw [hset]
      exact coneBall_hausdorff_lt_top hMF (e := e + 1) h W hW.isPrime hdimW
    have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    obtain ⟨hM0, -⟩ := coordBall_mass (n := n) (m := e + 1 + 1) (le_of_ringKrullDim_quotient W hdimW)
    have hfin : ∫⁻ y, ENNReal.ofReal (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) y) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [htop, ENNReal.mul_top hc0, ENNReal.mul_top hM0.ne'] at k1
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball).ne k1

    have hmeas : Measurable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x))) :=
      SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
        (continuous_abs.comp (continuous_fst.mul continuous_snd)).measurable measurable_const _
    have hnn : ∀ y, 0 ≤ chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) y :=
      fun y => finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> positivity
    exact ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).2 hfin⟩

end

end GroundTheory.Heights₂.Heights

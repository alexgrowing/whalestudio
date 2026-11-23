import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace IntegralIndep

variable {n d : ℕ}

theorem chartDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartAbsDens J A f φ y = chartPosDens J A f φ y + chartPosDens J A (-f) φ y ∧
      chartDens J A f φ y = chartPosDens J A f φ y - chartPosDens J A (-f) φ y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartAbsDens chartDens chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem chartPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) : 0 ≤ chartPosDens J A f φ y := by
  unfold chartPosDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)]
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp

theorem measurable_chartPosDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (chartPosDens J A f φ) :=
  SheetSumMeasurable.measurable_sheetSum hA (fun a b => max (a * b) 0)
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf φ

theorem chartInt_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by
  have h0 := chartPosDens_nonneg J A hA f φ
  have h1 := chartPosDens_nonneg J A hA (-f) φ
  have m0 := measurable_chartPosDens hA hf φ
  have m1 := measurable_chartPosDens hA hf.neg φ
  have habs : chartAbsDens J A f φ = fun y => chartPosDens J A f φ y + chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).1
  have hlin : ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (chartAbsDens J A f φ) ↔
      ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (chartPosDens J A f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (chartPosDens J A (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : chartDens J A f φ = fun y => chartPosDens J A f φ y - chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).2
  rw [chartInt, hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

end IntegralIndep

theorem IntegralIndep.proof (h : PosPartIndep.Statement) : IntegralIndep.Statement := by
  intro n d J A A' f φ hP hd hA hA' hf hφ hi
  have e0 := h n d J A A' f φ hP hd hA hA' hf hφ
  have e1 := h n d J A A' (-f) φ hP hd hA hA' hf.neg hφ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨iA', cA'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf φ
  have hi' : Integrable (chartAbsDens J A' f φ) := iA'.2 (by rw [← e0, ← e1]; exact iA.1 hi)
  exact ⟨hi', by rw [cA hi, cA' hi', e0, e1]⟩

end

end GroundTheory.Heights₂.Heights

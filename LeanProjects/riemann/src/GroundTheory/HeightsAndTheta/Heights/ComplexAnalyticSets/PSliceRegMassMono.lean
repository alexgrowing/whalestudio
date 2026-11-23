import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetLogNormDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm FormIntegralPositivity
open scoped ContDiff

noncomputable section

theorem SliceRegMassMono.proof (hM : SliceFormMass.Statement) : SliceRegMassMono.Statement := by
  intro n e h W F u' ℓ ε a b hW hF hℓ hε ha hb ha0 hab hb1
  unfold varInt
  split_ifs with hA
  swap
  · simp
  have hAfin := hA.choose_spec
  unfold chartInt

  have hint : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      ∀ (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
      (∀ k (t : ℂ) x, t ≠ 0 → ψ k (t • x) = ψ k x) → (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        fun k x => c k * Real.log (h.dualNorm x) + ψ k x) := by
    intro w hw hw1 c ψ hψ hψs
    refine Integrable.mono' (hM n e h W F ℓ hA.choose (fun _ => 1) c ψ hW hF hℓ hAfin
      (fun _ _ _ => rfl) continuousOn_const hψ hψs) ?_ (Eventually.of_forall fun y => ?_)
    · exact (SheetSumMeasurable.measurable_sheetSum hAfin (fun a b => a * b)
        (continuous_fst.mul continuous_snd).measurable hw _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
      simp only [chartDens, chartAbsDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      split_ifs
      · simp only [abs_mul, one_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hw1 x)
      · simp
  have h1 : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) := by
    intro w hw hw1
    have e1 : (fun (k : Fin (e + 1)) x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k *
        Real.log (h.dualNorm x) + (vecCons (fsLogReg h u' ε) fun _ _ => 0 :
          Fin (e + 1) → (Fin n → ℂ) → ℝ) k x) =
        vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) := by
      funext k x
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
    rw [← e1]
    refine hint w hw hw1 _ _ (fun k t x ht => ?_) fun k => ?_
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.fsLogReg_smul h u' ε ht x
      · rfl
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε
      · exact contDiffOn_const
  have h2 : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        fun _ x => Real.log (h.dualNorm x)) := by
    intro w hw hw1
    have := hint w hw hw1 (fun _ => 1) (fun _ _ => 0) (fun _ _ _ _ => rfl) fun _ => contDiffOn_const
    simpa using this
  have ha1 : ∀ x, |a x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [ha0 x], by linarith [hab x, hb1 x]⟩
  have hb1' : ∀ x, |b x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [ha0 x, hab x], hb1 x⟩
  rw [← integral_add (h1 a ha ha1) (h2 a ha ha1), ← integral_add (h1 b hb hb1') (h2 b hb hb1')]
  refine integral_mono ((h1 a ha ha1).add (h2 a ha ha1)) ((h1 b hb hb1').add (h2 b hb hb1'))
    fun y => ?_

  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
  simp only [chartDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp [linForm] at this
  split_ifs with hs
  · have hpos := dens_sum_nonneg SheetLogNormDens.proof h u' hε hs.choose_spec hx0
    have hmono := mul_le_mul_of_nonneg_right (hab x) hpos
    linarith
  · simp

end

end GroundTheory.Heights₂.Heights

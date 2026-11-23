import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceSectionTailMass.tendsto_tail {n d : ℕ} (h : HermNorm n) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (hMF : SliceMassFinite.Statement) (hprime : I.IsPrime) (hmem : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = (d : ℕ)) :
    Tendsto (fun k =>  varInt I d (fun x => 1 - sliceCut h k x)
      (fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0) := by
  classical
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose
  have hAf : IsFiniteProjection I A := hA.choose_spec
  have hfin : ∀ y, (fibre I A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d I A hprime hdim hAf y).2.1
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx hx0 => by
    subst hx0
    have := hx _ hmem
    simp [linForm] at this
  have hsm : ∀ _ : Fin d, SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x) := fun _ =>
    ⟨{0}ᶜ, isOpen_compl_singleton, hne, contDiffOn_log_dualNorm h⟩
  have hint := hMF n d h I ℓ A hprime hmem hdim hAf
  unfold chartInt
  have key := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (F := fun k => chartDens I A (fun x => 1 - sliceCut h k x) fun _ x => Real.log (h.dualNorm x))
    (chartAbsDens I A (fun _ => 1) fun _ x => Real.log (h.dualNorm x))
    (fun k => (SheetSumMeasurable.proof n d I A _ _ hprime hdim hAf
      (measurable_const.sub (SliceCut.measurable h k)) hsm).1.aestronglyMeasurable) hint
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rwa [integral_zero] at key
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with hs
    · have h01 := SliceCut.mem_Icc h k x
      rw [abs_mul, abs_mul, abs_one, one_mul, abs_of_nonneg (by linarith [h01.2])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [h01.1])
    · simp
  · unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    have hterm : ∀ x, Tendsto (fun k : ℕ => if hs : ∃ s, IsSheetAt I A x s then
        (1 - sliceCut h k x) * ReciprocityTheory.AnForm.maDens
          (fun i => (fun (_ : Fin d) x => Real.log (h.dualNorm x)) i ∘ hs.choose) y else 0)
        atTop (𝓝 0) := fun x => by
      split_ifs with hs
      · simpa using ((SliceCut.tendsto_one h x).const_sub 1).mul_const
          (ReciprocityTheory.AnForm.maDens (fun i => (fun (_ : Fin d) x => Real.log (h.dualNorm x)) i ∘ hs.choose) y)
      · exact tendsto_const_nhds
    simpa using tendsto_finsetSum (hfin y).toFinset fun x _ => hterm x

theorem SliceSectionTailMass.proof (hMF : SliceMassFinite.Statement) : SliceSectionTailMass.Statement := by
  intro n e h W F u' ℓ hW hF hu hℓ hℓP P hP
  obtain ⟨hprime, hdim, huJ⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨-, himg, -⟩ := SliceComponents.proof n W u' ℓ hW hℓP
  have hmin : P ⊔ Ideal.span {linForm ℓ - 1} ∈
      (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes := by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hP)
  exact SliceSectionTailMass.tendsto_tail h _ ℓ hMF hmin.1.1
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u' hu) hmin)

end

end GroundTheory.Heights₂.Heights

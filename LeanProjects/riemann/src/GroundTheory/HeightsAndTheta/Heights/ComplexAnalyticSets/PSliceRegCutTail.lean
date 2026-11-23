import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegCutTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceRegCutTail.proof (hM : SliceFormMass.Statement) : SliceRegCutTail.Statement := by
  classical
  intro n e h W F u' ℓ ε hW hF hℓ hε
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  set I := W ⊔ Ideal.span {linForm ℓ - 1} with hIdef
  have hmem : linForm ℓ - 1 ∈ I := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose
  have hAf : IsFiniteProjection I A := hA.choose_spec
  have hfin : ∀ y, (fibre I A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n (e + 1) I A hprime hdim hAf y).2.1
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx hx0 => by
    subst hx0
    have := hx _ hmem
    simp [linForm] at this
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ :=
    vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) with hφ
  have hsm : ∀ i, SmoothNear (zeroSet I) (φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨{x | x ≠ 0}, isOpen_ne, hne, by simpa [hφ] using contDiffOn_fsLogReg h u' hε⟩
    · exact ⟨{x | x ≠ 0}, isOpen_ne, hne, by simpa [hφ] using h.contDiffOn_log_dualNorm⟩
  have hint : Integrable (chartAbsDens I A (fun _ => 1) φ) := by
    rw [hφ, SliceCutOffLimit.vecCons_eq_affine h (fsLogReg h u' ε)]
    refine hM n e h W F ℓ A _ _ _ hW hF hℓ hAf (fun _ _ _ => rfl) continuousOn_const
      (fun k t x ht => ?_) (fun k => ?_)
    · refine Fin.cases ?_ (fun i => ?_) k
      · simpa using fsLogReg_smul h u' ε t x ht
      · simp
    · refine Fin.cases ?_ (fun i => ?_) k
      · simpa using contDiffOn_fsLogReg h u' hε
      · simpa using contDiffOn_const
  unfold chartInt
  have key := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (F := fun k => chartDens I A (fun x => 1 - sliceCut h k x) φ) (chartAbsDens I A (fun _ => 1) φ)
    (fun k => (SheetSumMeasurable.proof n (e + 1) I A _ _ hprime hdim hAf
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
        (1 - sliceCut h k x) * ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ hs.choose) y else 0)
        atTop (𝓝 0) := fun x => by
      split_ifs with hs
      · simpa using ((SliceCut.tendsto_one h x).const_sub 1).mul_const
          (ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ hs.choose) y)
      · exact tendsto_const_nhds
    simpa using tendsto_finsetSum (hfin y).toFinset fun x _ => hterm x

end

end GroundTheory.Heights₂.Heights

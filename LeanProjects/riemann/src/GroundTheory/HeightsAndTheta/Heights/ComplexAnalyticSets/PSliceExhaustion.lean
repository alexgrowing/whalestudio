import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceExhaustion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLelongError
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceExhaustion.varInt_tendsto_sliceCut {n d : ℕ} (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ) (hM : SliceMassFinite.Statement)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d)
    (hsm : SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x)) :
    Tendsto (fun k => varInt I d (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) atTop
      (𝓝 (varInt I d (fun _ => 1) fun _ x => Real.log (h.dualNorm x))) := by
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection I A
  · simp only [varInt, dif_pos hA]
    have := CutOffDominated.proof n d I hA.choose 1 (sliceCut h) (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) hI hdim hA.choose_spec one_ne_zero (SliceCut.measurable h)
      (SliceCut.mem_Icc h) (fun x _ _ => SliceCut.tendsto_one h x) continuousOn_const (fun _ => hsm)
      (hM n d h I ℓ hA.choose hI hℓ hdim hA.choose_spec)
    simpa only [mul_one] using this
  · simp only [varInt, dif_neg hA]
    exact tendsto_const_nhds

theorem SliceExhaustion.proof (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement)
    (hM : SliceMassFinite.Statement) (hE : SliceLelongError.Statement) : SliceExhaustion.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨-, himg, -⟩ := hC n J u ℓ hJ hℓW
  have hmem1 : ∀ K : Ideal (MvPolynomial (Fin n) ℂ), linForm ℓ - 1 ∈ K ⊔ Ideal.span {linForm ℓ - 1} :=
    fun _ => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨sliceCut h, SliceCut.contDiff h, SliceCut.hasCompactSupport h, SliceCut.mem_Icc h,
    SliceCut.tendsto_one h,
    SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hprime (hmem1 J) hdim
      (smoothNear_log_dualNorm_slice h J ℓ), fun W hW => ?_, hE n e h J F u ℓ hJ hF hu hℓ hℓW⟩
  have hmin : W ⊔ Ideal.span {linForm ℓ - 1} ∈
      (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes := by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hW)
  exact SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hmin.1.1 (hmem1 W)
    (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u hu) hmin)
    (smoothNear_log_dualNorm_slice h W ℓ)

end GroundTheory.Heights₂.Heights

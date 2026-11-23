import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelongCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceWeightMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceFormLelong.ne_zero_of_mem {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by
  rintro rfl
  have := hx _ hℓ
  simp [linForm] at this

theorem SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul {n d : ℕ} (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ)
    (hM : SliceWeightMassFinite.Statement) (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d)
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    Tendsto (fun k => varInt I d (fun x => sliceCut h k x * a x) fun _ x => Real.log (h.dualNorm x))
      atTop (𝓝 (varInt I d a fun _ x => Real.log (h.dualNorm x))) := by
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx => SliceFormLelong.ne_zero_of_mem hℓ hx
  have hsm : SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x) :=
    ⟨{0}ᶜ, isOpen_compl_singleton, hne, contDiffOn_log_dualNorm h⟩
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection I A
  · simp only [varInt, dif_pos hA]
    exact CutOffDominated.proof n d I hA.choose 1 (sliceCut h) a (fun _ x => Real.log (h.dualNorm x))
      hI hdim hA.choose_spec one_ne_zero (SliceCut.measurable h) (SliceCut.mem_Icc h)
      (fun x _ _ => SliceCut.tendsto_one h x) (hac.mono hne) (fun _ => hsm)
      (hM n d h I ℓ hA.choose a hI hℓ hdim hA.choose_spec ha hac)
  · simp only [varInt, dif_neg hA]
    exact tendsto_const_nhds

theorem SliceFormLelong.proof (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement)
    (hM : SliceWeightMassFinite.Statement) (hK : SliceFormLelongCompact.Statement)
    (hT : SliceRegTail.Statement) : SliceFormLelong.Statement := by
  intro n e h W F u' ℓ a hW hF hu hℓ hℓP ha hsa
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨-, himg, -⟩ := hC n W u' ℓ hW hℓP
  have hmem1 : ∀ K : Ideal (MvPolynomial (Fin n) ℂ), linForm ℓ - 1 ∈ K ⊔ Ideal.span {linForm ℓ - 1} :=
    fun _ => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hac : ContinuousOn a {x | x ≠ 0} := hsa.continuousOn
  have hmin : ∀ P ∈ (divCycle W u').support, P ⊔ Ideal.span {linForm ℓ - 1} ∈
      (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes := fun P hP => by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hP)

  have hL := (tendsto_finsetSum _ fun P hP =>
    (SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul h _ ℓ a hM (hmin P hP).1.1 (hmem1 P)
      (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u' hu) (hmin P hP)) ha hac).const_mul
        ((divCycle W u' P : ℕ) : ℝ)).sub
    (SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul h _ ℓ a hM hprime (hmem1 W) hdim ha hac)

  have hKk := fun k : ℕ => hK n e h W F u' ℓ (fun x => sliceCut h k x * a x) hW hF hu hℓ hℓP
    ⟨{x | x ≠ 0}, isOpen_compl_singleton, fun x hx => SliceFormLelong.ne_zero_of_mem (hmem1 W) hx,
      (SliceCut.contDiff h k).contDiffOn.mul hsa⟩ (SliceCut.hasCompactSupport h k).mul_right
  have key : ∀ δ x y z w : ℝ, |x - y| ≤ δ / 3 → |y - z| < δ / 3 → |z - w| < δ / 3 → |x - w| < δ := by
    intro δ x y z w h1 h2 h3
    have := abs_sub_le x y w
    have := abs_sub_le y z w
    linarith
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨K, hKt⟩ := hT n e h W F u' ℓ a hW hF hu hℓ hℓP ha hac (δ / 3) (by positivity)
  obtain ⟨k, hkK, hk⟩ :=
    ((eventually_ge_atTop K).and (Metric.tendsto_nhds.mp hL (δ / 3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.mp (hKk k) (δ / 3) (by positivity), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iic_mem_nhds one_pos)] with ε hε hε0 hε1
  rw [Real.dist_eq] at hε hk ⊢
  exact key δ _ _ _ _ (hKt k hkK ε ⟨hε0, hε1⟩) hε hk

end GroundTheory.Heights₂.Heights

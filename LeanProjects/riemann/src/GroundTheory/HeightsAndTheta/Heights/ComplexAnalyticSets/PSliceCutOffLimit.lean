import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutBoundary
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceCutOffLimit.vecCons_eq_affine {n e : ℕ} (h : HermNorm n) (G : (Fin n → ℂ) → ℝ) :
    (vecCons G fun (_ : Fin e) x => Real.log (h.dualNorm x)) =
      fun k x => (vecCons (0 : ℝ) fun (_ : Fin e) => (1 : ℝ)) k * Real.log (h.dualNorm x) +
        (vecCons G fun (_ : Fin e) (_ : Fin n → ℂ) => (0 : ℝ)) k x := by
  funext k x
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

theorem SliceCutOffLimit.proof (hI : SliceIdeal.Statement) (hM : SliceFormMass.Statement)
    (hB : SliceCutBoundary.Statement) : SliceCutOffLimit.Statement := by
  intro n e h W g ℓ hW hg hℓ
  obtain ⟨hJ, hdim, -⟩ := hI n (e + 1) W g ℓ hW hg hℓ
  refine ⟨sliceCut h, SliceCut.contDiff h, SliceCut.hasCompactSupport h, fun F G hF0 hG0 hF hG => ?_⟩
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A
  · simp only [varInt, dif_pos hA]
    have hAs := hA.choose_spec
    generalize hA.choose = A at hAs ⊢
    have hne : zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) ⊆ {x | x ≠ 0} := by
      rintro x hx rfl
      have h1 := hx (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))
      simp [linForm] at h1
    have hnear : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
        SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f := fun f hf =>
      ⟨{x | x ≠ 0}, isOpen_ne, hne, hf⟩
    have hpot : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
        ∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}))
          (vecCons f (fun (_ : Fin e) x => Real.log (h.dualNorm x)) i) := by
      intro f hf i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hnear f hf
      · simpa using hnear _ h.contDiffOn_log_dualNorm
    have hint : ∀ f f' : (Fin n → ℂ) → ℝ, (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) →
        ContDiffOn ℝ ∞ f {x | x ≠ 0} → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f' (t • x) = f' x) →
        ContDiffOn ℝ ∞ f' {x | x ≠ 0} →
        Integrable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
          (vecCons f' fun _ x => Real.log (h.dualNorm x))) := by
      intro f f' hf0 hf hf'0 hf'
      rw [SliceCutOffLimit.vecCons_eq_affine h f']
      refine hM n e h W g ℓ A f _ _ hW hg hℓ hAs hf0 hf.continuousOn (fun k t x ht => ?_) (fun k => ?_)
      · refine Fin.cases ?_ (fun i => ?_) k
        · simpa using hf'0 t x ht
        · simp
      · refine Fin.cases ?_ (fun i => ?_) k
        · simpa using hf'
        · simpa using contDiffOn_const
    have hD := fun (f : (Fin n → ℂ) → ℝ) (f' : (Fin n → ℂ) → ℝ) hf0 hf hf'0 hf' =>
      CutOffDominated.proof n (e + 1) _ A 1 (sliceCut h) f (vecCons f' fun _ x => Real.log (h.dualNorm x))
        hJ hdim hAs one_ne_zero (SliceCut.measurable h) (SliceCut.mem_Icc h)
        (fun x _ _ => SliceCut.tendsto_one h x) (hf.continuousOn.mono hne) (hpot f' hf')
        (hint f f' hf0 hf hf'0 hf')
    refine ⟨hD F G hF0 hF hG0 hG, ?_⟩
    have h1 := (hD G F hG0 hG hF0 hF).add (hB n e h W g ℓ A F G hW hg hℓ hAs hF0 hG0 hF hG)
    simpa using h1
  · simp only [varInt, dif_neg hA]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

end GroundTheory.Heights₂.Heights

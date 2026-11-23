import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeGraphCover
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSmoothLocalGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal NNReal

noncomputable section

theorem coneSet_hausdorff_null_of_dim_lt {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by
  set g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.transpose h.mat)⁻¹)
  have hu : IsUnit (Matrix.transpose h.mat).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hsub : coneSet h J ⊆ g '' zeroSetEuc J := by
    intro y hy
    refine ⟨WithLp.toLp 2 (h.pointOf y), hy, ?_⟩
    ext i
    simp [g, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
  calc Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (g '' zeroSetEuc J)
      ≤ (‖g‖₊ : ℝ≥0∞) ^ ((2 * d : ℕ) : ℝ) * Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J) :=
        g.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [NullSmaller.proof n d J hd, mul_zero]

theorem ConeGraphCover.proof (hDim : ConeFiniteFibreDim.Statement) (hTan : ConeTangentDim.Statement)
    (hLoc : ConeSmoothLocalGraph.Statement) : ConeGraphCover.Statement := by
  intro n m h J hJ hm hmn hfib
  have e0 : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (finCongr (Nat.add_sub_cancel' hmn).symm).trans finSumFinEquiv.symm
  rcases (hDim n m h J hJ hm hmn hfib).lt_or_eq with hlt | heq
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    exact measure_mono_null Set.sdiff_subset (coneSet_hausdorff_null_of_dim_lt h J m hlt)

  set S := {y | y ∈ coneSet h J ∧ finrank ℂ (coneTangent h J y) = m} with hSdef
  have hbad : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ S) = 0 := by
    have hae := hTan n m h J hJ hm hmn hfib
    rw [ae_iff] at hae
    refine measure_mono_null ?_ (nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hae.le))
    intro y hy
    exact ⟨fun h' => hy.2 ⟨hy.1, h'⟩, hy.1⟩

  have hloc := fun y (hy : y ∈ S) => hLoc n m h J hJ.isPrime heq y hy.1 hy.2
  have : Nonempty (Fin n ≃ Fin m ⊕ Fin (n - m)) := ⟨e0⟩
  choose! E Om Ph U hUo hyU hCU hΩ hΦ hG hT using hloc

  obtain ⟨T, hTS, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable S U hUo
  have hScov : S ⊆ ⋃ y ∈ T, graphPt (E y) (Ph y) '' Om y := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ S, U z := Set.mem_biUnion hy (hyU y hy)
    rw [← hTU] at hy'
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hz (hCU z (hTS hz) ⟨hy.1, hyz⟩)
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => ?_⟩
    have hy' := hScov hyS
    simp [hT0] at hy'
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hfS : ∀ i, f i ∈ S := fun i => hTS (by rw [hf]; exact Set.mem_range_self i)
    refine ⟨fun i => E (f i), fun i => Om (f i), fun i => Ph (f i),
      fun i => ⟨hΩ _ (hfS i), hΦ _ (hfS i), hG _ (hfS i), hT _ (hfS i)⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => hy.2 ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hScov hyS)
    rw [hf] at hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.2 ⟨i, hyz⟩

end

end GroundTheory.Heights₂.Heights

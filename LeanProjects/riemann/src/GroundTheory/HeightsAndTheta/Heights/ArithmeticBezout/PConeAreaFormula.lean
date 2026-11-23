import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeGraphCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem volume_null_of_hausdorff_null {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hμ : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin m))) =
      Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [hdim]
  rw [hμ] at hs
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)) hs

theorem encard_iUnion_disjoint_nat {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem volume_linProj_image_null {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by
  refine volume_null_of_hausdorff_null (nonpos_iff_eq_zero.1 ?_)
  have hL := (LinearMap.toContinuousLinearMap (linProjₗ π)).lipschitz.hausdorffMeasure_image_le
    (d := ((2 * m : ℕ) : ℝ)) (by positivity) s
  rw [LinearMap.coe_toContinuousLinearMap', hs, mul_zero] at hL
  exact hL

theorem ConeAreaFormula.proof (hCover : ConeGraphCover.Statement) (hArea : GraphAreaFibre.Statement) :
    ConeAreaFormula.Statement := by
  intro n m h J hJ hm hmn hfin π g hg
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D := disjointed S
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hSm
  have hDS : ∀ i, D i ⊆ S i := disjointed_subset S
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed S
  have hU : ⋃ i, D i = ⋃ i, S i := iUnion_disjointed
  have hUC : ⋃ i, D i ⊆ coneSet h J := Set.iUnion_subset fun i => (hDS i).trans (hpc i).2.2.1
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, D i) = 0 := by
    rw [hU]; exact hnull
  have hCae : coneSet h J =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, fibreCount, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end

end GroundTheory.Heights₂.Heights

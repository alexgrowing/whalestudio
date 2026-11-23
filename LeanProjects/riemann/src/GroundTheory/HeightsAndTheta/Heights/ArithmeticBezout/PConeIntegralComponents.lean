import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeComponents
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMeetNull
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConePtsIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PComplexFibreCycle
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace ConeIntegralComponents

variable {n : ℕ}

theorem eq_zero_of_pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit (Matrix.transpose h.mat) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
  have h0 : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [Matrix.mulVec_zero]; exact hy)
  ext i
  simpa using congrFun h0 i

theorem coneBall_subset (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsRadical) :
    coneBall h J ⊆ {0} ∪ ⋃ W ∈ (fundCycle J).support, coneBall h W := by
  classical
  rintro y ⟨hy1, hyJ⟩
  have : (RingHom.ker (eval (h.pointOf y))).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le
    (fun q hq => (RingHom.mem_ker).2 (hyJ q hq) : J ≤ RingHom.ker (eval (h.pointOf y)))
  by_cases hrel : IsRelevant W
  · right
    have hmem : W ∈ (fundCycle J).support := by
      rw [Finsupp.mem_support_iff]
      unfold fundCycle
      rw [Finsupp.onFinset_apply, if_pos ⟨hWmin, hrel⟩, localMult_eq_one_of_isRadical hJ hWmin]
      exact one_ne_zero
    exact Set.mem_biUnion hmem ⟨hy1, fun q hq => (RingHom.mem_ker).1 (hWle hq)⟩
  · left
    refine eq_zero_of_pointOf_eq_zero h (funext fun j => ?_)
    have hX : X j ∈ W := by
      by_contra hj
      exact hrel ⟨j, hj⟩
    simpa using (RingHom.mem_ker).1 (hWle hX)

theorem hausdorffMeasure_zero (e : ℕ) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  refine hausdorffMeasure_of_dimH_lt ?_
  rw [dimH_singleton, ENNReal.coe_natCast]
  exact_mod_cast (by omega : 0 < 2 * (e + 1))

theorem setIntegral_finset_biUnion_ae {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (t : Finset ι) {s : ι → Set X} (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ (s i ∩ s j) = 0) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn f (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdis : AEDisjoint μ (s a) (⋃ i ∈ t, s i) := by
      change μ (s a ∩ ⋃ i ∈ t, s i) = 0
      rw [Set.inter_iUnion₂]
      refine (measure_biUnion_null_iff t.countable_toSet).2 fun i hi => ?_
      exact hd a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union₀ hdis (Finset.measurableSet_biUnion t hs').nullMeasurableSet
        (hf a (Finset.mem_insert_self a t)) (integrableOn_finset_iUnion.2 hf'),
      ih hs' (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) hf']

theorem exists_chowForm_components (hEx : ChowFormExists.Statement) (hBC : ChowFormBaseChange.Statement)
    {e : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1)) :
    ∃ g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ,
      ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, IsProjPrime W ∧ IsChowForm W (e + 1) (g W) := by
  have hI := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  obtain ⟨f, hf⟩ := hEx ℚ n (e + 1) _ hI (ObjectsChow.GenericFibreDim.proof n (e + 1) P hP)
  obtain ⟨hproj, c, -, g, hg, -⟩ := hBC ℚ n (e + 1) _ f (Rat.castHom ℂ) hI hf
  rw [← ComplexFibreCycle.complexFibreIdeal_eq_map] at hproj hg
  exact ⟨g, fun W hW => ⟨hproj W hW, hg W hW⟩⟩

end ConeIntegralComponents

open ConeIntegralComponents in

theorem ConeIntegralComponents.proof (hEx : ChowFormExists.Statement)
    (hBC : ChowFormBaseChange.Statement) (hDim : ConeDimOfChowForm.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hMeet : ConeMeetNull.Statement) :
    ConeIntegralComponents.Statement := by
  intro n e h P u hP hu
  classical
  set S := (fundCycle (complexFibreIdeal P)).support with hS
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ
  obtain ⟨g, hg⟩ := exists_chowForm_components hEx hBC hP
  have hdimW : ∀ W ∈ S, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
    fun W hW => (hDim ℂ n (e + 1) W (g W) (hg W hW).1 (hg W hW).2).le
  have hJW : ∀ W ∈ S, complexFibreIdeal P ≤ W :=
    fun W hW => (mem_minimalPrimes_of_mem_fundCycle_support hW).1.2
  have hae : coneBall h (complexFibreIdeal P) =ᵐ[μ] ⋃ W ∈ S, coneBall h W := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (hausdorffMeasure_zero e), ?_⟩
    · rcases coneBall_subset h (complexFibreIdeal_isRadical hP) hy.1 with h0 | h1
      · exact h0
      · exact absurd h1 hy.2
    · have hsub : (⋃ W ∈ S, coneBall h W) ⊆ coneBall h (complexFibreIdeal P) :=
        Set.iUnion₂_subset fun W hW y (hy : y ∈ coneBall h W) =>
          (⟨hy.1, fun q hq => hy.2 q (hJW W hW hq)⟩ : y ∈ coneBall h (complexFibreIdeal P))
      rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  have key := setIntegral_finset_biUnion_ae (μ := μ) (f := fun y => fsLog h u (h.pointOf y)) S
    (fun W _ => measurableSet_coneBall h W)
    (fun W hW W' hW' hne => hMeet n e h W W' (hg W hW).1.isPrime (hg W' hW').1.isPrime hne
      (hdimW W hW) (hdimW W' hW'))
    (fun W hW => hInt n e h W (g W) u (hg W hW).1 (hg W hW).2 (hu W hW))
  unfold coneIntegral
  rw [← Finset.sum_div]
  congr 1
  change ∑ W ∈ S, ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂μ =
    ∫ y in coneBall h (complexFibreIdeal P), fsLog h u (h.pointOf y) ∂μ
  rw [setIntegral_congr_set hae, key]

end GroundTheory.Heights₂.Heights

import Mathlib
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import ReciprocityTheory.SemistableReduction.IntCoresA

namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory ReciprocityTheory.MultiplicativeHeights

noncomputable def hintPt {D n : ℕ} (t0 : Fin n → ℂ) (z : BlockSphere D n) :
    Fin (D + 1) × Fin n → ℂ :=
  fun v => Fin.cases (t0 v.2) (fun i => spherePoint (z i) v.2) v.1

theorem hint_mpSplit (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0)
      (blockSphereProb (D + 1) n) ((sphereProb n).prod (blockSphereProb D n)) := by
  unfold blockSphereProb
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => sphereProb n) 0

private theorem isProbabilityMeasure_sphereProb' (n : ℕ) (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold sphereProb
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := Module.finrank_pos
  have h1 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos.ne') (Metric.measure_ball_pos _ _ one_pos).ne'
  have h2 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite h1 h2

theorem hint_mpTail (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ)
      (blockSphereProb (D + 1) n) (blockSphereProb D n) := by
  haveI := isProbabilityMeasure_sphereProb' n hn
  haveI : SFinite (blockSphereProb D n) := by
    unfold blockSphereProb
    infer_instance
  have h := (measurePreserving_snd (μ := sphereProb n) (ν := blockSphereProb D n)).comp
    (hint_mpSplit D n hn)
  have e : (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ) =
      Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0) := by
    funext z i
    first
      | rfl
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; done)
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; rfl)
      | exact congrArg z (by simp)
  rw [e]
  exact h

theorem hint_blockPoint_eq {D n : ℕ} (z : BlockSphere (D + 1) n) :
    blockPoint z = hintPt (spherePoint (z 0)) (fun i : Fin D => z i.succ) := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero => simp [blockPoint, hintPt]
  | succ i => simp [blockPoint, hintPt]

theorem hint_eval_indep {D n : ℕ} {a : Fin (D + 1) → ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ}
    (hq : IsMultiHomogeneous a q) (ha : a 0 = 0) (x y : Fin (D + 1) × Fin n → ℂ)
    (hxy : ∀ v : Fin (D + 1) × Fin n, v.1 ≠ 0 → x v = y v) :
    MvPolynomial.eval x q = MvPolynomial.eval y q := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.1 = 0
  · have h0 : s v = 0 := by
      have hsum := hq s hs 0
      rw [ha] at hsum
      have hle : s (0, v.2) ≤ ∑ j : Fin n, s (0, j) :=
        Finset.single_le_sum (f := fun j => s (0, j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      have hz : s (0, v.2) = 0 := by omega
      have hv' : v = (0, v.2) := Prod.ext hv rfl
      rw [hv']
      exact hz
    rw [h0, pow_zero, pow_zero]
  · rw [hxy v hv]

theorem hint_continuous_pt {D n : ℕ} (t0 : Fin n → ℂ) :
    Continuous fun z : BlockSphere D n => hintPt t0 z := by
  apply continuous_pi
  rintro ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    simp only [hintPt, Fin.cases_zero]
    exact continuous_const
  | succ i =>
    simp only [hintPt, Fin.cases_succ]
    unfold spherePoint
    fun_prop

theorem hint_logInt_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    Integrable (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) := by
  have hmeas : AEStronglyMeasurable
      (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) :=
    ((continuous_norm.comp ((MvPolynomial.continuous_eval q).comp
      (hint_continuous_pt t0))).measurable.log).aestronglyMeasurable
  rw [← (hint_mpTail D n hn).integrable_comp hmeas]
  refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a q hq0 hq).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_ae_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    ∀ᵐ z ∂(blockSphereProb D n), MvPolynomial.eval (hintPt t0 z) q ≠ 0 := by
  have hA : MeasurableSet {z : BlockSphere D n | MvPolynomial.eval (hintPt t0 z) q = 0} :=
    (isClosed_eq ((MvPolynomial.continuous_eval q).comp (hint_continuous_pt t0))
      continuous_const).measurableSet
  rw [ae_iff]
  simp only [not_not]
  rw [← (hint_mpTail D n hn).measure_preimage hA.nullMeasurableSet]
  have h0 := ae_blockSphere_eval_ne_zero (D + 1) n a q hq0 hq
  rw [ae_iff] at h0
  refine measure_mono_null (fun z hz => ?_) h0
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
  simp only [Set.mem_ofPred_eq, not_not]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  · exact hz
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_fubini {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {F : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    Integrable (fun z : BlockSphere D n =>
      ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb n))
      (blockSphereProb D n) := by
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := D) hn
  set G : UnitSphereC n × BlockSphere D n → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hint : Integrable G ((sphereProb n).prod (blockSphereProb D n)) := by
    rw [← (hint_mpSplit D n hn).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  exact hint.integral_prod_right

theorem hint_lin_ae {n : ℕ} (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ s ∂(sphereProb n), ∑ j, c j * spherePoint s j ≠ 0 := by
  classical
  set Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ :=
    ∑ j, c j • (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap with hLc
  have hL : ∀ x : EuclideanSpace ℂ (Fin n), Lc x = ∑ j, c j * WithLp.ofLp x j := by
    intro x
    simp [hLc]
  set H : Submodule ℝ (EuclideanSpace ℂ (Fin n)) := LinearMap.ker (Lc.restrictScalars ℝ) with hH
  have hHtop : H ≠ ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ H := htop ▸ Submodule.mem_top
    rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL] at hmem
    simp at hmem
    exact hj hmem
  have hvol : (volume : Measure (EuclideanSpace ℂ (Fin n))) H = 0 :=
    Measure.addHaar_submodule _ H hHtop
  have hA : MeasurableSet {s : UnitSphereC n | ¬ (∑ j, c j * spherePoint s j ≠ 0)} := by
    simp only [not_not]
    exact (isClosed_eq (by unfold spherePoint; fun_prop) continuous_const).measurableSet
  rw [ae_iff]
  unfold sphereProb
  refine ProbabilityTheory.cond_absolutelyContinuous ?_
  rw [Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℂ (Fin n)))) hA]
  apply mul_eq_zero_of_right
  refine measure_mono_null ?_ hvol
  rintro _ ⟨r, _, _, ⟨s, hs, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq, not_not] at hs
  show r • (s : EuclideanSpace ℂ (Fin n)) ∈ H
  refine H.smul_mem r ?_
  rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL]
  simpa [spherePoint] using hs

end ReciprocityTheory.ChartRestriction.G.T0

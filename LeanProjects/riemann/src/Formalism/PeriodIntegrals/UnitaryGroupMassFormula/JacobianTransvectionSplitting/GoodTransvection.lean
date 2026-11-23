import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.FactorOneOfDiscrete

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def phiM (M : Matrix ι ι F) (hM : IsUnit M.det) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM]
  map_add' x y := Matrix.mulVec_add M x y
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

def chiM (M : Matrix ι ι F) (hM : IsUnit M.det) : ℝ≥0 :=
  letI := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  addEquivAddHaarChar (phiM M hM)

theorem chiM_spec [mF : MeasurableSpace (ι → F)] [hB : BorelSpace (ι → F)] (M : Matrix ι ι F)
    (hM : IsUnit M.det) (ν : Measure (ι → F)) [ν.IsAddHaarMeasure] (S : Set (ι → F)) :
    ν ((fun x => M *ᵥ x) '' S) = chiM M hM * ν S := by
  obtain rfl : mF = borel (ι → F) := hB.measurable_eq
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM M hM = addEquivAddHaarChar (phiM M hM) := rfl
  have himg : (fun x => M *ᵥ x) '' S = (phiM M hM).symm ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (phiM M hM).symm ((phiM M hM) x) = x := (phiM M hM).symm_apply_apply x
      rw [show M *ᵥ x = (phiM M hM) x from rfl, this]
      exact hx
    · intro hy
      exact ⟨(phiM M hM).symm y, hy, (phiM M hM).apply_symm_apply y⟩
  have key := addEquivAddHaarChar_smul_preimage ν (X := S) (phiM M hM).symm
  rw [addEquivAddHaarChar_symm, ENNReal.smul_def, smul_eq_mul] at key
  rw [himg, e, ← key, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos (phiM M hM)).ne', ENNReal.coe_one, one_mul]

theorem chiM_mul (A B : Matrix ι ι F) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hAB : IsUnit (A * B).det) : chiM (A * B) hAB = chiM A hA * chiM B hB := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : ∀ (N : Matrix ι ι F) (hN : IsUnit N.det), chiM N hN = addEquivAddHaarChar (phiM N hN) :=
    fun _ _ => rfl
  rw [e, e, e, show phiM (A * B) hAB = (phiM B hB).trans (phiM A hA) from
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm, addEquivAddHaarChar_trans, mul_comm]

theorem chiM_one (h : IsUnit (1 : Matrix ι ι F).det) : chiM (1 : Matrix ι ι F) h = 1 := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM (1 : Matrix ι ι F) h = addEquivAddHaarChar (phiM 1 h) := rfl
  rw [e, show phiM 1 h = ContinuousAddEquiv.refl _ from
    ContinuousAddEquiv.ext fun x => Matrix.one_mulVec x, addEquivAddHaarChar_refl]

theorem chiM_congr {A B : Matrix ι ι F} (e : A = B) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    chiM A hA = chiM B hB := by
  subst e
  rfl

theorem chiM_pos (M : Matrix ι ι F) (hM : IsUnit M.det) : 0 < chiM M hM := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  exact addEquivAddHaarChar_pos (phiM M hM)

theorem exists_test_set [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (ν : Measure (ι → F))
    [ν.IsAddHaarMeasure] : ∃ K : Set (ι → F), MeasurableSet K ∧ ν K ≠ 0 ∧ ν K ≠ ∞ := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : ι → F)
  exact ⟨K, hKc.isClosed.measurableSet, (MeasureTheory.Measure.measure_pos_of_mem_nhds (μ := ν) hK0).ne', hKc.measure_lt_top.ne⟩

theorem chiM_diagOne (hD : DiagOne) (i : ι) (a : F) (ha : a ≠ 0)
    (h : IsUnit (diagonal (Function.update (1 : ι → F) i a)).det) :
    (chiM (diagonal (Function.update (1 : ι → F) i a)) h : ℝ≥0∞) = modF F a := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  obtain ⟨K, hKm, hK0, hKt⟩ := exists_test_set (Measure.addHaar : Measure (ι → F))
  have h1 := chiM_spec _ h (Measure.addHaar : Measure (ι → F)) K
  have h2 := hD F ι i a ha (Measure.addHaar : Measure (ι → F)) inferInstance K hKm
  have hfun : (fun x => diagonal (Function.update (1 : ι → F) i a) *ᵥ x) = fun x => Function.update x i (a * x i) := by
    funext x j
    by_cases hj : j = i
    · subst hj
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Function.update_of_ne hj]
  rw [hfun] at h1
  rw [h1] at h2
  exact (ENNReal.mul_left_inj hK0 hKt).mp h2

def Good (M : Matrix ι ι F) : Prop :=
  ∀ h : IsUnit M.det, (chiM M h : ℝ≥0∞) = modF F M.det

theorem good_mul {A B : Matrix ι ι F} (hA0 : A.det ≠ 0) (hB0 : B.det ≠ 0)
    (hA : Good A) (hB : Good B) : Good (A * B) := by
  intro h
  rw [chiM_mul A B (isUnit_iff_ne_zero.mpr hA0) (isUnit_iff_ne_zero.mpr hB0) h, ENNReal.coe_mul,
    hA, hB, det_mul, modF_mul hA0 hB0]

theorem good_one : Good (1 : Matrix ι ι F) := by
  intro h
  rw [chiM_one, det_one, modF_of_ne (one_ne_zero : (1 : F) ≠ 0)]
  simp

theorem good_diagonal (hD : DiagOne) (D : ι → F) (hD0 : ∀ i, D i ≠ 0) : Good (diagonal D) := by
  classical
  have key : ∀ s : Finset ι, ∀ D : ι → F, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → Good (diagonal D) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro D _ h1
      have : D = 1 := funext fun i => h1 i (Finset.notMem_empty i)
      rw [this, show diagonal (1 : ι → F) = 1 from diagonal_one]
      exact good_one
    | @insert i s hi ih =>
      intro D hD0 h1
      have hsplit : diagonal D = diagonal (Function.update D i 1) * diagonal (Function.update (1 : ι → F) i (D i)) := by
        rw [diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj]
      have hdet1 : (diagonal (Function.update (1 : ι → F) i (D i))).det = D i := by
        rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
        simp
      have hne : ∀ j, Function.update D i 1 j ≠ 0 := fun j => by
        by_cases hj : j = i
        · subst hj
          simp
        · rw [Function.update_of_ne hj]
          exact hD0 j
      rw [hsplit]
      refine good_mul ?_ (by rw [hdet1]; exact hD0 i) (ih _ hne fun j hj => ?_) fun h => ?_
      · rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun j _ => hne j
      · by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · rw [chiM_diagOne hD i (D i) (hD0 i) h, hdet1]
  exact key Finset.univ D hD0 fun i hi => absurd (Finset.mem_univ i) hi

theorem transvection_conj {i j : ι} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    transvection i j c = diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 *
      diagonal (Function.update (1 : ι → F) i c⁻¹) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hk : k = i <;> by_cases hl : l = i <;> simp_all <;>
    split_ifs <;> simp_all [eq_comm]

theorem good_transvection (i j : ι) (hij : i ≠ j) (c : F) : Good (transvection i j c) := by
  have hT : ∀ c : F, IsUnit (transvection i j c).det := fun c => by
    rw [Matrix.det_transvection_of_ne (i := i) (j := j) hij c]
    exact isUnit_one
  have h1u : IsUnit (1 : Matrix ι ι F).det := by
    rw [det_one]
    exact isUnit_one
  have hdd : ∀ c : F, (diagonal (Function.update (1 : ι → F) i c)).det = c := fun c => by
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hDu : ∀ c : F, c ≠ 0 → IsUnit (diagonal (Function.update (1 : ι → F) i c)).det := fun c hc => by
    rw [hdd]
    exact isUnit_iff_ne_zero.mpr hc
  have hmod1 : modF F 1 = 1 := by
    have := good_one h1u
    rw [chiM_one, det_one] at this
    simpa using this.symm
  have hconst : ∀ c : F, c ≠ 0 →
      chiM (transvection i j c) (hT c) = chiM (transvection i j 1) (hT 1) := by
    intro c hc
    have hDD : diagonal (Function.update (1 : ι → F) i c) * diagonal (Function.update (1 : ι → F) i c⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk
        simp [hc]
      · simp [Function.update_of_ne hk]
    have hprod : chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc)) = 1 := by
      rw [← chiM_mul _ _ _ _ (by rw [hDD]; exact h1u), chiM_congr hDD _ h1u, chiM_one]
    have hu1 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1).det := by
      rw [det_mul]
      exact (hDu c hc).mul (hT 1)
    have hu2 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 * diagonal (Function.update (1 : ι → F) i c⁻¹)).det := by
      rw [← transvection_conj hij hc]
      exact hT c
    rw [chiM_congr (transvection_conj hij hc) (hT c) hu2,
      chiM_mul _ _ hu1 (hDu _ (inv_ne_zero hc)) hu2, chiM_mul _ _ (hDu c hc) (hT 1) hu1]
    calc chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (transvection i j 1) (hT 1) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))
        = chiM (transvection i j 1) (hT 1) * (chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))) := by ring
      _ = chiM (transvection i j 1) (hT 1) := by rw [hprod, mul_one]
  have hc1 : chiM (transvection i j c) (hT c) = 1 := by
    by_cases hc : c = 0
    · subst hc
      rw [chiM_congr (Matrix.transvection_zero (i := i) (j := j)) (hT 0) h1u, chiM_one]
    · have hsq : chiM (transvection i j c) (hT c) * chiM (transvection i j c) (hT c) =
          chiM (transvection i j (c + c)) (hT (c + c)) := by
        rw [← chiM_mul _ _ (hT c) (hT c)
          (by rw [Matrix.transvection_mul_transvection_same (i := i) (j := j) hij]; exact hT _)]
        exact chiM_congr (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c c) _ _
      have hx0 := (chiM_pos _ (hT c)).ne'
      by_cases h2 : c + c = 0
      · have h0 : chiM (transvection i j (c + c)) (hT (c + c)) = 1 := by
          rw [chiM_congr (show transvection i j (c + c) = 1 by rw [h2, Matrix.transvection_zero])
            (hT (c + c)) h1u, chiM_one]
        rw [h0] at hsq
        exact (pow_left_inj₀ (chiM_pos _ (hT c)).le zero_le_one two_ne_zero).mp (by rw [sq, hsq, one_pow])
      · rw [hconst (c + c) h2, ← hconst c hc] at hsq
        exact mul_left_cancel₀ hx0 (hsq.trans (mul_one _).symm)
  intro h
  rw [chiM_congr rfl h (hT c), hc1, Matrix.det_transvection_of_ne (i := i) (j := j) hij c, hmod1]
  simp

theorem linModulus_of (hD : DiagOne) : LinModulus := by
  intro F _ _ _ _ _ _ ι _ _ _ _ M hM ν hν S _
  have hG : Good M := Matrix.diagonal_transvection_induction_of_det_ne_zero Good M hM
    (fun D hD0 => good_diagonal hD D fun i => by
      rw [det_diagonal] at hD0
      exact Finset.prod_ne_zero_iff.mp hD0 i (Finset.mem_univ i))
    (fun t => good_transvection t.i t.j t.hij t.c)
    (fun A B hA hB gA gB => good_mul hA hB gA gB)
  rw [chiM_spec M (isUnit_iff_ne_zero.mpr hM) ν S, hG]

end PI.NglqJacSplitW

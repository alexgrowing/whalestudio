import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SmoothSumLeftRightMulOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SumDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.QuadraticFormGradientFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem scal_mem {E : Type} [Field E] [NumberField E] {a : ℕ} {y : Lie E a} (hy : y ∈ invSet E a) :
    sc (Matrix.of y) • y ∈ invSet E a := by
  have hc : sc (Matrix.of y) ≠ 0 := (Real.exp_pos _).ne'
  have hy' : IsUnit (Matrix.of y) := hy
  have h : IsUnit (sc (Matrix.of y) • Matrix.of y) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 _ hc).map (algebraMap ℝ (Matrix (Fin a) (Fin a) (Cinf E)))).mul hy'
  exact h

private theorem chart_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (gsum L (pg P)) g y = msum (fun v : lat L g => pt (rt g) v.1) P (sc (Matrix.of y) • y) := by
  obtain ⟨u, hu⟩ := hy
  obtain rfl : y = toL u.val := hu.symm
  rw [chart_val, (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg P)).2.1 g u]
  refine tsum_congr fun v => congrArg (pg P) ?_
  exact (Matrix.vecMul_smul _ _ _).symm

theorem UpperTheory.hermitian_chart_scalar_invariance :
    ThSm := by
  intro E _ _ _ a ha L hL P hP
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hS : ContDiffOn ℝ ∞ (fun y : Lie E a => sc (Matrix.of y) • y) (invSet E a) := hs.smul contDiffOn_id
  refine ⟨⟨gsum L (pg P), fun g => ?_⟩, rfl, fun X => ?_⟩
  · exact ((UpperTheory.smooth_sum_left_right_mul_order E a _ _ N (hN g) P hP).comp hS fun y hy => scal_mem hy).congr
      fun y hy => chart_eq ha L P g hy
  · have ho : oneL E a ∈ invSet E a := isUnit_one
    have hn : invSet E a ∈ nhds (oneL E a) := isOpen_invSet.mem_nhds ho
    have h1' : sc (Matrix.of (oneL E a)) = 1 := h1
    have hsd : DifferentiableAt ℝ (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
      (hs.contDiffAt hn).differentiableAt (by simp)
    have hSd := hsd.hasFDerivAt.smul (hasFDerivAt_id (oneL E a))
    let Z : Lie E a := X + (-ell E a X) • oneL E a
    let T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) := (Matrix.vecMulLinear (Matrix.of Z)).restrictScalars ℝ
    obtain ⟨Q, hQ, hT⟩ := (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 T
    refine ⟨Q, hQ, funext fun g => ?_⟩
    obtain ⟨-, hF, hF'⟩ := UpperTheory.sum_der E a _ _ N (hN g) P hP _ ho
    have e : chart (gsum L (pg P)) g =ᶠ[nhds (oneL E a)]
        msum (fun v : lat L g => pt (rt g) v.1) P ∘ fun y : Lie E a => sc (Matrix.of y) • y :=
      Filter.eventually_of_mem hn fun y hy => chart_eq ha L P g hy
    have hF1 : HasFDerivAt (msum (fun v : lat L g => pt (rt g) v.1) P)
        (fderiv ℝ (msum (fun v : lat L g => pt (rt g) v.1) P) (oneL E a)) (sc (Matrix.of (oneL E a)) • oneL E a) := by
      rw [h1', one_smul]
      exact hF.hasFDerivAt
    have hc := HasFDerivAt.comp (f := fun y : Lie E a => sc (Matrix.of y) • y) (oneL E a) hF1 hSd
    change fderiv ℝ (chart (gsum L (pg P)) g) (oneL E a) X = _
    rw [e.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, h1', one_smul, hd, id]
    rw [hF']
    refine tsum_congr fun v => ?_
    rw [← hT]
    have e1 : pt (rt g) v.1 ᵥ* Matrix.of (oneL E a) = pt (rt g) v.1 := Matrix.vecMul_one _
    rw [e1]
    rfl

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.trWeak :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (A : ι → H →L[ℂ] H) (A₀ Z : H →L[ℂ] H), IsTraceClass Z → (∀ i, ‖A i‖ ≤ 1) →
      (∀ x y, Tendsto (fun i => ⟪x, A i y⟫_ℂ) l (𝓝 ⟪x, A₀ y⟫_ℂ)) → Tendsto (fun i => trace (A i ∘L Z)) l (𝓝 (trace (A₀ ∘L Z))) := by
  intro H _ _ _ ι l A A₀ Z hZ hA hw
  obtain ⟨S, T, hS, hT, rfl⟩ := hZ.exists_comp
  let b := stdHilbertBasis ℂ H
  have e : ∀ B : H →L[ℂ] H, trace (B ∘L S ∘L T) = ∑' m, ⟪ContinuousLinearMap.adjoint T (b m), B (S (b m))⟫_ℂ := fun B => by
    have h1 : trace ((B ∘L S) ∘L T) = trace (T ∘L (B ∘L S)) := trace_comp_comm_of_isHilbertSchmidt (hS.comp_left B) hT
    have h2 := ((isTraceClass_comp hT (hS.comp_left B)).hasSum_trace b).tsum_eq
    simp only [ContinuousLinearMap.adjoint_inner_left]
    exact h1.trans h2.symm
  simp only [e]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖ContinuousLinearMap.adjoint T (b m)‖ ^ 2 + ‖S (b m)‖ ^ 2)
    ((hT.adjoint.hasSum_norm_sq b).summable.add (hS.hasSum_norm_sq b).summable) (fun m => hw _ _) (Eventually.of_forall fun i m => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  have h3 : ‖A i (S (b m))‖ ≤ ‖S (b m)‖ := by simpa using (A i).le_of_opNorm_le (hA i) (S (b m))
  nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint T (b m)‖ - ‖S (b m)‖), norm_nonneg (ContinuousLinearMap.adjoint T (b m)),
    norm_nonneg (S (b m)), mul_le_mul_of_nonneg_left h3 (norm_nonneg (ContinuousLinearMap.adjoint T (b m)))]

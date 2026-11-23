import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.carLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ →
      (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) ∧ M.swap.Carries (ContinuousLinearMap.adjoint X) (sharp κ) ∧
      ∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → M.P' (Ioi (T + ρ)) ∘L X ∘L (1 - M.P (Ioi T)) = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX
  obtain ⟨c1, c2, -⟩ := convLaws κ hk
  refine ⟨fun t h => ?_, fun v => ?_, fun ρ T hρ => ?_⟩
  · obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, hX, hX, M.hJ', neg_neg]
    exact congrArg M.J' (DFunLike.congr_fun (c1 t) u)
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective h
    show ⟪M.J u, ContinuousLinearMap.adjoint X (M.J' v)⟫_ℂ = ⟪M.J u, M.J (conv (sharp κ) v)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right, hX, M.J'.inner_map_map, M.J.inner_map_map, ← (convAdj κ hk).2.1,
      ContinuousLinearMap.adjoint_inner_right]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    have e : (1 - M.P (Ioi T)) (M.J u) = M.J (cut V (Iic T) u) := by
      have h1 := (cutLaws (V := V) (Iic T) (Ioi T) measurableSet_Iic measurableSet_Ioi)
      have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, h1.2.2.2.1] at h2
      have h3 : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun h2 u
      simp only [Sc.P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
      show M.J u - M.J (cut V (Ioi T) (M.J.symm (M.J u))) = _
      rw [M.J.symm_apply_apply, ← map_sub, sub_eq_of_eq_add h3]
    show M.P' (Ioi (T + ρ)) (X ((1 - M.P (Ioi T)) (M.J u))) = 0
    rw [e, hX]
    show M.J' (cut W (Ioi (T + ρ)) (M.J'.symm (M.J' _))) = 0
    rw [M.J'.symm_apply_apply]
    have := DFunLike.congr_fun (c2 ρ T hρ) u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [this, map_zero]

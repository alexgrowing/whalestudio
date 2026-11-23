import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ShNull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)

private theorem P_app (s : Set ℝ) (h : H) : M.P s h = M.J (cut V s (M.J.symm h)) := rfl

private theorem one' (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) : M.P s ∘L M.P t = M.P (s ∩ t) ∧ IsSelfAdjoint (M.P s) ∧ ‖M.P s‖ ≤ 1 ∧
    (Disjoint s t → M.P (s ∪ t) = M.P s + M.P t) ∧ ∀ a : ℝ, M.F.U a ∘L M.P s = M.P ((fun x => x + a) ⁻¹' s) ∘L M.F.U a := by
  obtain ⟨c1, c2, c3, -, -, c4, c5, -⟩ := cutLaws (V := V) s t hs ht
  refine ⟨?_, ?_, ?_, fun hd => ?_, fun a => ?_⟩
  · ext h
    simp only [ContinuousLinearMap.comp_apply, P_app, M.J.symm_apply_apply, ← c1]
  · refine LinearMap.IsSymmetric.isSelfAdjoint fun x y => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective x
    obtain ⟨v, rfl⟩ := M.J.surjective y
    simp only [ContinuousLinearMap.coe_coe, P_app, M.J.symm_apply_apply, M.J.inner_map_map]
    exact c2.isSymmetric u v
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
    rw [P_app, M.J.norm_map, one_mul]
    exact (c4 _).trans_eq (M.J.symm.norm_map h)
  · ext h
    simp only [P_app, c3 hd, ContinuousLinearMap.add_apply, map_add]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    simp only [ContinuousLinearMap.comp_apply, P_app, M.J.symm_apply_apply, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun (c5 a) u)
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.projLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), M.F.Null ∧ M.swap.swap.F.U = M.F.U ∧ (∀ s, M.swap.P' s = M.P s) ∧ (∀ T T', M.swap.abelian₂ T' T = M.abelian₂ T T') ∧
      (∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t → M.P s ∘L M.P t = M.P (s ∩ t) ∧ IsSelfAdjoint (M.P s) ∧ ‖M.P s‖ ≤ 1 ∧
        (Disjoint s t → M.P (s ∪ t) = M.P s + M.P t) ∧ ∀ a : ℝ, M.F.U a ∘L M.P s = M.P ((fun x => x + a) ⁻¹' s) ∘L M.F.U a ∧
          M.F.U a ∘L M.P' s = M.P' ((fun x => x - a) ⁻¹' s) ∘L M.F.U a) ∧ M.P ∅ = 0 ∧ M.P univ = 1 ∧
      ∀ T T', 2 * M.T₀ ≤ T + T' → M.P (Ioi T) ∘L M.P' (Ioi T') = 0 ∧ M.P' (Ioi T') ∘L M.P (Ioi T) = 0 ∧
        M.abelian₂ T T' ∘L M.abelian₂ T T' = M.abelian₂ T T' ∧ IsSelfAdjoint (M.abelian₂ T T') ∧ ‖M.abelian₂ T T'‖ ≤ 1 ∧
        M.abelian₂ T T' ∘L M.P (Ioi T) = 0 ∧ M.P (Ioi T) ∘L M.abelian₂ T T' = 0 ∧ M.abelian₂ T T' ∘L M.P' (Ioi T') = 0 ∧ M.P' (Ioi T') ∘L M.abelian₂ T T' = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  have hn : M.F.Null := fun h h' => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    obtain ⟨u', rfl⟩ := M.J.surjective h'
    simp only [M.hJ, M.J.inner_map_map]
    exact shNull u u'
  refine ⟨hn, funext fun t => by simp [Sc.swap, Flow.rev], fun _ => rfl, fun T T' => sub_right_comm _ _ _,
    fun s t hs ht => ⟨(one' M s t hs ht).1, (one' M s t hs ht).2.1, (one' M s t hs ht).2.2.1, (one' M s t hs ht).2.2.2.1,
      fun a => ⟨(one' M s t hs ht).2.2.2.2 a, ?_⟩⟩, ?_, ?_, fun T T' hT => ?_⟩
  · have := (one' M.swap s t hs ht).2.2.2.2 (-a)
    simpa [Sc.swap, Flow.rev, Sc.P', sub_eq_add_neg] using this
  · ext h
    rw [P_app, (cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.2.1]; simp
  · ext h
    rw [P_app, (cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.1]; simp
  · obtain ⟨a1, a2, -⟩ := one' M (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
    obtain ⟨b1, b2, -⟩ := one' M.swap (Ioi T') (Ioi T') measurableSet_Ioi measurableSet_Ioi
    rw [inter_self] at a1 b1
    change M.P' (Ioi T') ∘L M.P' (Ioi T') = M.P' (Ioi T') at b1
    change IsSelfAdjoint (M.P' (Ioi T')) at b2
    have o1 : M.P (Ioi T) * M.P' (Ioi T') = 0 := by
      ext h
      refine ext_inner_left ℂ fun y => ?_
      have hc := (cutLaws (V := W) (Ioi (2 * M.T₀ - T)) (Ioi T') measurableSet_Ioi measurableSet_Ioi).1
      rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at hc
      have e : M.P' (Ioi T') h = M.J' (cut W (Ioi (2 * M.T₀ - T)) (cut W (Ioi T') (M.J'.symm h))) :=
        congrArg M.J' (DFunLike.congr_fun hc _).symm
      rw [ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, e, P_app, M.causal]; simp
    have o2 : M.P' (Ioi T') * M.P (Ioi T) = 0 := by
      have := congrArg star o1
      rwa [star_mul, a2.star_eq, b2.star_eq, star_zero] at this
    change M.P (Ioi T) * M.P (Ioi T) = _ at a1
    change M.P' (Ioi T') * M.P' (Ioi T') = _ at b1
    have l1 : M.abelian₂ T T' * M.P (Ioi T) = 0 := by rw [Sc.abelian₂, sub_mul, sub_mul, a1, o2]; simp
    have l2 : M.P (Ioi T) * M.abelian₂ T T' = 0 := by rw [Sc.abelian₂, mul_sub, mul_sub, a1, o1]; simp
    have l3 : M.abelian₂ T T' * M.P' (Ioi T') = 0 := by rw [Sc.abelian₂, sub_mul, sub_mul, b1, o1]; simp
    have l4 : M.P' (Ioi T') * M.abelian₂ T T' = 0 := by rw [Sc.abelian₂, mul_sub, mul_sub, b1, o2]; simp
    have l0 : M.abelian₂ T T' * M.abelian₂ T T' = M.abelian₂ T T' := by
      conv_lhs => rw [show M.abelian₂ T T' * M.abelian₂ T T' = M.abelian₂ T T' * (1 - M.P (Ioi T) - M.P' (Ioi T')) from rfl]
      rw [mul_sub, mul_sub, l1, l3]; simp
    have sa : IsSelfAdjoint (M.abelian₂ T T') := ((IsSelfAdjoint.one _).sub a2).sub b2
    exact ⟨o1, o2, l0, sa, (IsStarProjection.mk l0 sa).norm_le _, l1, l2, l3, l4⟩

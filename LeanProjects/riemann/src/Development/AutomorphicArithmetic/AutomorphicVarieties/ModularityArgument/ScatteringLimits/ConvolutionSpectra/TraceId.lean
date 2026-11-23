import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandTC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TwoProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceId :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T a : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → 0 ≤ a →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) →
      trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace (M.P' (Ioc T (T + a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc (T - a) T)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T a hψ hT ha htc
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨t1, -, -, -, -⟩ := bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)
  obtain ⟨-, t2, t3, -, -⟩ := bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)
  have hcomm := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).2.2.2.2 M.F (M.F.U (-a))
    (fun t h => by rw [← M.F.add, ← M.F.add, add_comm])
  set Ψ := M.F.av (fun t => (ψ t : ℂ)) with hΨ
  set Y := Ψ ∘L X with hY
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have mc : ∀ x y : ℝ, MeasurableSet (Ioc x y) := fun _ _ => measurableSet_Ioc
  have s1 : M.P' (Ioi T) = M.P' (Ioc T (T + a)) + M.P' (Ioi (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI (T + a))).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  have s2 : M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) + M.P (Ioi T) := by
    have := (hP _ _ (mc (T - a) T) (mI T)).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  obtain ⟨-, -, l0, -, -, -, -, l3, l4⟩ := hL T T (by linarith)
  obtain ⟨-, -, m0, -, -, m1, m2, -, -⟩ := hL (T - a) (T + a) (by linarith)
  have e0 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mc T (T + a))).1
    rwa [inter_self] at this
  have e1 : M.P' (Ioi T) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mI T) (mc T (T + a))).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e2 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioi T) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI T)).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  have e3 : M.P (Ioi (T - a)) ∘L M.P (Ioc (T - a) T) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mI (T - a)) (mc (T - a) T)).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e4 : M.P (Ioc (T - a) T) ∘L M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mc (T - a) T) (mI (T - a))).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  obtain ⟨tc, key⟩ := twoProj (M.abelian₂ T T) (M.P' (Ioc T (T + a))) (M.abelian₂ (T - a) (T + a)) (M.P (Ioc (T - a) T)) Y
    (by simp only [Sc.abelian₂, s1, s2]; abel) l0 e0 m0 (by simpa using (hP _ _ (mc (T - a) T) (mc (T - a) T)).1)
    (by rw [← e1, ← ContinuousLinearMap.comp_assoc, l3, ContinuousLinearMap.zero_comp])
    (by rw [← e2, ContinuousLinearMap.comp_assoc, l4, ContinuousLinearMap.comp_zero])
    (by rw [← e3, ← ContinuousLinearMap.comp_assoc, m1, ContinuousLinearMap.zero_comp])
    (by rw [← e4, ContinuousLinearMap.comp_assoc, m2, ContinuousLinearMap.comp_zero]) htc t2 t3 t1
  rw [key]
  congr 1
  have u1 : ∀ h, M.F.U a (M.abelian₂ T T h) = M.abelian₂ (T - a) (T + a) (M.F.U a h) := fun h => by
    obtain ⟨x1, x2⟩ := (hP _ _ (mI T) (mI T)).2.2.2.2 a
    have y1 : (fun x : ℝ => x + a) ⁻¹' Ioi T = Ioi (T - a) := by ext x; simp [sub_lt_iff_lt_add]
    have y2 : (fun x : ℝ => x - a) ⁻¹' Ioi T = Ioi (T + a) := by ext x; simp [lt_sub_iff_add_lt]
    rw [y1] at x1; rw [y2] at x2
    have z1 := DFunLike.congr_fun x1 h
    have z2 := DFunLike.congr_fun x2 h
    simp only [ContinuousLinearMap.comp_apply] at z1 z2
    simp only [Sc.abelian₂, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, z1, z2]
  have inv1 : ∀ h, M.F.U (-a) (M.F.U a h) = h := fun h => by rw [← M.F.add, neg_add_cancel, M.F.zero]
  have inv2 : ∀ h, M.F.U a (M.F.U (-a) h) = h := fun h => by rw [← M.F.add, add_neg_cancel, M.F.zero]
  have u2 : ∀ h, M.F.U (-a) (M.abelian₂ (T - a) (T + a) h) = M.abelian₂ T T (M.F.U (-a) h) := fun h => by
    conv_lhs => rw [← inv2 h, ← u1, inv1]
  have hYU : ∀ h, Y (M.F.U a h) = M.F.U (-a) (Y h) := fun h => by
    show Ψ (X (M.F.U a h)) = M.F.U (-a) (Ψ (X h))
    rw [(carLaws M X κ hk hX).1]
    exact (DFunLike.congr_fun hcomm _).symm
  have := trace_comp_comm (tc.comp_left (M.F.U (-a))) (M.F.U a)
  have f1 : M.F.U a ∘L (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) =
      M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a) := by
    ext h; simp only [ContinuousLinearMap.comp_apply, inv2]
  have f2 : (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) ∘L M.F.U a =
      M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L Y ∘L M.abelian₂ T T := by
    ext h
    show M.F.U (-a) (M.abelian₂ (T - a) (T + a) (Y (M.abelian₂ (T - a) (T + a) (M.F.U a h)))) = M.abelian₂ T T (M.F.U (-(2 * a)) (Y (M.abelian₂ T T h)))
    rw [← u1, hYU, u2, ← M.F.add]
    congr 3; ring
  rwa [f1, f2] at this

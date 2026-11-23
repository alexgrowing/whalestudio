import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ContAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ScalSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandHS :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (φ : ℝ → ℂ) (a b : ℝ), Continuous φ → HasCompactSupport φ → a ≤ b →
      IsHilbertSchmidt (X ∘L M.P (Ioc a b)) ∧ hsNorm (X ∘L M.P (Ioc a b)) ^ 2 = (b - a) * ∑ i, ‖kv κ (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
      IsHilbertSchmidt (M.F.av φ ∘L M.P (Ioc a b)) ∧
      hsNorm (M.F.av φ ∘L M.P (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ V * ∫ x, ‖φ x‖ ^ 2) ∧
      trace (ContinuousLinearMap.adjoint (M.F.av φ ∘L M.P (Ioc a b)) ∘L (X ∘L M.P (Ioc a b))) =
        ∫ y in a..b, ∑ i, M.cor (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX φ a b h1 h2 hab
  have cU : ∀ (F : Flow H) (A : V →L[ℂ] H), Continuous fun y => F.U y ∘L A := fun F A =>
    continuous_clm_apply.2 fun e => F.cont (A e)
  let A : V →L[ℂ] H := (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) ∘L kv κ
  let A' : V →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sv V fun x => φ (-x)
  have pa : ∀ u, M.P (Ioc a b) (M.J u) = M.J (cut V (Ioc a b) u) := fun u => congrArg M.J (congrArg _ (M.J.symm_apply_apply u))
  obtain ⟨s1, s2, s3⟩ := scalSpec (V := V) φ h1 h2
  have hi : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have y1 : ∀ u : L V, (X ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.U y ∘L A) (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec κ hk).2 a b u
    rw [ContinuousLinearMap.comp_apply, pa, hX, i2]
    refine ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ' y _).symm)
  have y2 : ∀ u : L V, (M.F.av φ ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.rev.U y ∘L A') (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec _ s1).2 a b u
    have c := ((avSpec (shF V)).2.2.2 φ hi).2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm
    have c' : ∀ v, M.F.av φ (M.J v) = M.J ((shF V).av φ v) := fun v => (DFunLike.congr_fun c v).symm
    rw [ContinuousLinearMap.comp_apply, pa, c', s2, i2]
    refine ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    rw [s3]
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ (-y) _).symm)
  obtain ⟨k1, k2, k3⟩ := kp M.J a b _ _ _ _ hab (cU M.F A) (cU M.F.rev A') y1 y2
  obtain ⟨k4, k5, -⟩ := kp M.J a b _ _ _ _ hab (cU M.F.rev A') (cU M.F.rev A') y2 y2
  refine ⟨k1, ?_, k4, ?_, ?_⟩
  · rw [k2]
    simp [M.F.norm, A]
  · rw [k5]
    have m2 : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    have n : ∀ i, ‖(M.F.rev.U 0 ∘L A') (stdOrthonormalBasis ℂ V i)‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := fun i => by
      show ‖M.F.rev.U 0 (M.J (sv V (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i)))‖ ^ 2 = _
      rw [Flow.norm, M.J.norm_map, ((svSpec (V := V)).1 _ m2 _).2, (stdOrthonormalBasis ℂ V).orthonormal.1,
        integral_neg_eq_self fun x => ‖φ x‖ ^ 2]
      simp
    simp only [ContinuousLinearMap.comp_apply, Flow.norm] at n ⊢
    simp [n, mul_left_comm]
  · rw [k3]
    refine intervalIntegral.integral_congr fun y _ => Finset.sum_congr rfl fun i _ => ?_
    show ⟪M.F.U (-y) (M.J _), M.F.U y (M.J' _)⟫_ℂ = ⟪M.J _, M.F.U (2 * y) (M.J' _)⟫_ℂ
    rw [← (avSpec M.F).1, ContinuousLinearMap.adjoint_inner_left, ← M.F.add, two_mul]
    rfl

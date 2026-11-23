import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.convAdj :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → Ker (sharp κ) ∧ ContinuousLinearMap.adjoint (conv κ) = conv (sharp κ) ∧
      ∀ z : ℂ, symb (sharp κ) z = ContinuousLinearMap.adjoint (symb κ (-conj z)) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have hs : Ker (sharp κ) := by
    refine ⟨(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).continuous.comp (hk.1.comp continuous_neg), ?_⟩
    exact (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun A : V →L[ℂ] W => ContinuousLinearMap.adjoint A) (map_zero _)
  refine ⟨hs, ?_, fun z => ?_⟩
  · refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v u => ?_).symm
    rw [(convSpec _ hk u).2.2, (convSpec _ hs v).2.2, ← integral_inner (convSpec _ hk u).2.1, ← inner_conj_symm,
      ← integral_inner (convSpec _ hs v).2.1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [inner_conj_symm]
    rw [L2.inner_def, L2.inner_def, ← integral_add_right_eq_self _ t]
    refine integral_congr_ae ?_
    have q := (measurePreserving_add_right volume t).quasiMeasurePreserving
    filter_upwards [q.ae ((sharp κ (-t)).coeFn_compLpL (sh W (-t) v)), q.ae (sh_ae W (-t) v), (κ t).coeFn_compLpL (sh V t u),
      sh_ae V t u] with x a b c d
    rw [a, b, c, d, add_neg_cancel_right, sharp, neg_neg, ContinuousLinearMap.adjoint_inner_left]
  · have hi : ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
        [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
        (k : ℝ → A →L[ℂ] B), Ker k → ∀ z : ℂ, Integrable fun t : ℝ => Complex.exp (z * t) • k t := fun k hk z =>
      (Continuous.smul (f := fun t : ℝ => Complex.exp (z * t)) (by fun_prop) hk.1).integrable_of_hasCompactSupport hk.2.smul_left
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v u => ?_
    rw [symb, symb, ContinuousLinearMap.integral_apply (hi _ hs _), ContinuousLinearMap.integral_apply (hi _ hk _),
      ← integral_inner ((hi _ hk _).apply_continuousLinearMap u), ← inner_conj_symm,
      ← integral_inner ((hi _ hs _).apply_continuousLinearMap v), ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, map_mul, inner_conj_symm, sharp, neg_neg,
      ContinuousLinearMap.adjoint_inner_left, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 2
    push_cast
    ring

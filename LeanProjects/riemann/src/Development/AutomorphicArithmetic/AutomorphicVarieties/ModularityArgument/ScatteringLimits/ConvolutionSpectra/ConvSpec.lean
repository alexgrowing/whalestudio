import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.AeIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.convSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, (∀ᵐ x : ℝ, conv κ u x = ∫ t : ℝ, κ t (u (x + t))) ∧
      Integrable (fun t => (κ t).compLpL 2 volume (sh V t u)) ∧ conv κ u = ∫ t, (κ t).compLpL 2 volume (sh V t u) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  let c : (V →L[ℂ] W) →L[ℂ] (L V →L[ℂ] L W) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A
  have hi : ∀ u : L V, Integrable (fun t => (κ t).compLpL 2 volume (sh V t u)) := fun u => by
    refine Continuous.integrable_of_hasCompactSupport ((c.continuous.comp hk.1).clm_apply ((shF V).cont u)) ?_
    refine hk.2.mono fun t ht h0 => ht ?_
    show c (κ t) (sh V t u) = 0
    rw [h0, map_zero, ContinuousLinearMap.zero_apply]
  have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let A : L V →ₗ[ℂ] L W :=
    { toFun := fun u => ∫ t, (κ t).compLpL 2 volume (sh V t u)
      map_add' := fun x y => by simp only [map_add]; exact integral_add (hi x) (hi y)
      map_smul' := fun a x => by simp only [map_smul, RingHom.id_apply]; exact integral_smul a _ }
  have hb : ∀ u, ‖A u‖ ≤ (∫ t, ‖κ t‖) * ‖u‖ := fun u => by
    rw [← integral_mul_const]
    refine norm_integral_le_of_norm_le (hk1.norm.mul_const _) (Eventually.of_forall fun t => ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u]
    gcongr
    exact ContinuousLinearMap.norm_compLpL_le _
  have hae : ∀ u : L V, ∀ᵐ x : ℝ, (A u : L W) x = ∫ t : ℝ, κ t (u (x + t)) := fun u => by
    refine ae_integral volume _ (hi u) (fun p => κ p.1 (u (p.2 + p.1))) ?_ (Eventually.of_forall fun t => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (u : ℝ → V) (p.2 + p.1)) (volume.prod volume) :=
        ((Lp.stronglyMeasurable u).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable
      exact (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable h1
    · filter_upwards [(κ t).coeFn_compLpL (sh V t u), sh_ae V t u] with x a b
      rw [a, b]
  have sp := Classical.epsilon_spec (p := fun C : L V →L[ℂ] L W => ∀ u, ∀ᵐ x : ℝ, C u x = ∫ t : ℝ, κ t (u (x + t)))
    ⟨A.mkContinuous _ hb, hae⟩
  refine fun u => ⟨sp u, hi u, Lp.ext ?_⟩
  filter_upwards [sp u, hae u] with x a b
  exact a.trans b.symm

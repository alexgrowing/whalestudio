import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem exists_orthogonal_projection {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) : ∃ P, IsOrthogonalProjectionTwoLines J J' P := by
  let S : Submodule ℂ H := (LinearMap.range J.toLinearMap ⊔ LinearMap.range J'.toLinearMap)ᗮ
  refine ⟨Sᗮ.starProjection, isSelfAdjoint_starProjection _, (Sᗮ.isIdempotentElem_starProjection).eq, fun h => ?_⟩
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  simp only [S]
  rw [← Submodule.inf_orthogonal,
    Submodule.mem_inf, Submodule.mem_orthogonal, Submodule.mem_orthogonal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u => h1 _ ⟨u, rfl⟩, fun v => h2 _ ⟨v, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rintro _ ⟨u, rfl⟩; exact h1 u, by rintro _ ⟨v, rfl⟩; exact h2 v⟩

private theorem cutZero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (T : ℝ) (u : L V) : ∀ᵐ x : ℝ, x ≤ T → UpperTheory.V.Z.IntegralApplyAeEq.cut V (Ioi T) u x = 0 := by
  obtain ⟨h1, -, -, -, -, -, -, h2, -⟩ := UpperTheory.V.Z.IntegralApplyAeEq.cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  rw [inter_self] at h1
  filter_upwards [(h2 _).1 (DFunLike.congr_fun h1 u)] with x hx hT
  exact hx (not_lt.2 hT)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.projEx :
    ProjExC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A'
  have hc := (pairFacts K μ μ₂ τ₁ τ₂ hp D d d' A A').2
  refine ⟨exists_orthogonal_projection _ _, fun T hT => ⟨_, (UpperTheory.V.Z.IntegralApplyAeEq.truncEq A.J A'.J T _ fun u v => ?_).2 rfl⟩⟩
  refine hc T _ _ (cutZero T u) ?_
  filter_upwards [cutZero T v] with x hx hx'
  exact hx (by linarith)

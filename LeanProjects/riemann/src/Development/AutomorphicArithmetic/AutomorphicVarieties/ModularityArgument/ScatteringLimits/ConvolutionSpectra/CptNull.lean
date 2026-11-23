import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cptNull :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (K : H →L[ℂ] H) (x : ι → H) (C : ℝ), IsCompactOperator K → (∀ i, ‖x i‖ ≤ C) →
      (∀ y, Tendsto (fun i => ⟪y, x i⟫_ℂ) l (𝓝 0)) → Tendsto (fun i => K (x i)) l (𝓝 0) := by
  intro H _ _ _ ι l K x C hK hb hw
  obtain ⟨S, hS, hsub⟩ := hK.image_closedBall_subset_compact C
  refine hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun i => hsub ⟨x i, by simpa using hb i, rfl⟩) ?_
  intro y _ hy
  have h1 : Tendsto (fun i => ⟪y, K (x i)⟫_ℂ) l (𝓝 0) := by
    simpa [ContinuousLinearMap.adjoint_inner_left] using hw (ContinuousLinearMap.adjoint K y)
  have h2 : MapClusterPt ⟪y, y⟫_ℂ l (fun i => ⟪y, K (x i)⟫_ℂ) :=
    hy.continuousAt_comp (f := fun z => ⟪y, z⟫_ℂ) (by fun_prop)
  have h3 : ⟪y, y⟫_ℂ = 0 := eq_of_nhds_neBot (h2.clusterPt.mono h1).neBot
  exact inner_self_eq_zero.1 h3

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.main :
    PositivityTheory.Rg.Tf.IntegralApplyAeEq.Main := by
  intro H V W _ _ _ _ _ _ _ _ _ D
  haveI := FiniteDimensional.complete ℂ V
  haveI := FiniteDimensional.complete ℂ W
  obtain ⟨M, hT, hJ, hJ', hL⟩ := model D
  have act : ∀ Y β β', Ker β → Ker β' → Conv D.J D.J Y β → Conv D.J' D.J' Y β' → M.Acts Y β β' := fun Y β β' k k' c c' =>
    ⟨fun u => by rw [hJ, hJ]; exact c u _ (convSpec β k u).1, fun v => by rw [hJ', hJ']; exact c' v _ (convSpec β' k' v).1⟩
  obtain ⟨N, hN⟩ := nUnit M D.B D.β D.β' D.β_ker D.β'_ker D.β_unit D.β'_unit (act _ _ _ D.β_ker D.β'_ker D.B_J D.B_J')
    (hT ▸ D.compact D.T₀ _ le_rfl ((hL _ _ le_rfl).2 rfl))
  refine ⟨N, fun Y β β' k k' c c' => nInt M _ hN Y β β' k k' (act _ _ _ k k' c c'), ?_⟩
  intro X Λ κ T K hk hc hT' hΛ htc hb
  obtain rfl := (hL T Λ hT').1 hΛ
  have hX : M.Carries X κ := fun u => by rw [hJ, hJ']; exact hc u _ (convSpec κ hk u).1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨ψ, δ, -, hδ, hψ, h1⟩ := traceNear M X κ hk hX T (hT ▸ hT') htc ε hε
  have h2 := traceSm M N hN X κ hk hX ψ δ T K hδ hψ (hT ▸ hT') htc hb
  rw [hT] at h2
  rw [norm_sub_rev] at h1
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add h1 h2).trans_eq (add_comm _ _))

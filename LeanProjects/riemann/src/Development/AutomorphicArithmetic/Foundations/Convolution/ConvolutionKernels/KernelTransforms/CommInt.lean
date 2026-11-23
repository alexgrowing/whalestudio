import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.commInt :
    ∀ (G G₁ G₂ H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : UnitaryRep G H) (p₁ : G₁ →* G) (h₁ : Continuous p₁) (p₂ : G₂ →* G) (h₂ : Continuous p₂)
      (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
      (f₁ : CompactlySupportedContinuousMap G₁ ℂ) (f₂ : CompactlySupportedContinuousMap G₂ ℂ),
      (∀ w v : H, ⟪w, (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁)
          ((π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) v)⟫_ℂ =
        ∫ a, ∫ b, f₁ a * f₂ b * ⟪w, π (p₁ a * p₂ b) v⟫_ℂ ∂μ₂ ∂μ₁) ∧
      ((∀ a b, p₁ a * p₂ b = p₂ b * p₁ a) →
        (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) ∘L (π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) =
        (π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) ∘L (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁)) := by
  intro G G₁ G₂ H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π p₁ h₁ p₂ h₂ μ₁ _ μ₂ _ f₁ f₂
  have key : ∀ {L : Type} [Group L] [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L] (σ : UnitaryRep L H) (μ : Measure L)
      [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap L ℂ) (w u : H),
      ⟪w, σ.integrated μ (UnitaryRep.ccToL1 μ f) u⟫_ℂ = ∫ g, f g * ⟪w, σ g u⟫_ℂ ∂μ := by
    intro L _ _ _ _ σ μ _ f w u
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 μ f).mono fun g hg => ?_)
    exact congrArg (· * ⟪w, σ g u⟫_ℂ) hg
  refine ⟨fun w v => ?_, fun hc => ?_⟩
  · rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    dsimp only
    rw [UnitaryRep.compHom_apply, UnitaryRep.inner_map_right, key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [UnitaryRep.compHom_apply, UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply, mul_assoc]
  · have step : ∀ b, π (p₂ b) ∘L (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) =
        (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) ∘L π (p₂ b) := fun b => by
      refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
      intro a v
      simp only [UnitaryRep.compHom_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hc]
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro b v
    exact (DFunLike.congr_fun (step b) v).symm

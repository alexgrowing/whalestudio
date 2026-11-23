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

theorem UpperTheory.ConvolutionTheory.Tf.adjInt :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
      (f g : CompactlySupportedContinuousMap G ℂ), (∀ x, g x = conj (f x⁻¹)) →
      ContinuousLinearMap.adjoint (π.integrated μ (UnitaryRep.ccToL1 μ f)) = π.integrated μ (UnitaryRep.ccToL1 μ g) ∧
      ‖π.integrated μ (UnitaryRep.ccToL1 μ f)‖ ≤ ∫ x, ‖f x‖ ∂μ ∧ ∫ x, ‖g x‖ ∂μ = ∫ x, ‖f x‖ ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ π μ _ _ f g hg
  have hf1 : ((UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  have hg1 : ((UnitaryRep.ccToL1 μ g : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] g := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  refine ⟨?_, ?_, ?_⟩
  · rw [UnitaryRep.adjoint_integrated]
    congr 1
    apply Lp.ext
    have h2 : (fun x => (UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) x⁻¹) =ᵐ[μ] fun x => f x⁻¹ :=
      (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp hf1
    filter_upwards [UnitaryRep.coeFn_involution μ (UnitaryRep.ccToL1 μ f), h2, hg1] with x h1 h2 h3
    rw [h1, h2, h3, hg]
  · refine (π.norm_integrated_le μ _).trans (le_of_eq ?_)
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (hf1.mono fun x hx => by simp only [hx])
  · rw [← integral_inv_eq_self (fun x => ‖f x‖) μ]
    congr 1
    ext x
    rw [hg, RCLike.norm_conj]

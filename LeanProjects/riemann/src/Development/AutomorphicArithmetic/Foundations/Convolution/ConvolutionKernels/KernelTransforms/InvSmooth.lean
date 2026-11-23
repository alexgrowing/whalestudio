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

section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Manifold ContDiff Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_inv {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun fun g => f g⁻¹ := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf (contMDiff_id.inv)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_cont {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

private theorem UpperTheory.ConvolutionTheory.Tf.deriv_zero {f : G → ℂ} {U : Set G} (hU : IsOpen U) (h0 : ∀ g ∈ U, f g = 0)
    (X : 𝔤) : ∀ g ∈ U, h.rightDeriv X f g = 0 := by
  intro g hg
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := by
    letI := h.chartedSpace
    exact continuous_const.mul h.contMDiff_expG.continuous
  have he : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
    have : (fun Y : 𝔤 => g * h.expG Y) ⁻¹' U ∈ 𝓝 (0 : 𝔤) :=
      (hU.preimage hc).mem_nhds (by simpa using hg)
    filter_upwards [this] with Y hY using h0 _ hY
  simp [IsExpLieAlgebra.rightDeriv, he.fderiv_eq]

private theorem UpperTheory.ConvolutionTheory.Tf.act_zero {U : Set G} (hU : IsOpen U)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    ∀ f : h.smoothFuns (F := ℂ), (∀ g ∈ U, (f : G → ℂ) g = 0) →
      ∀ g ∈ U, (h.rightUAction u f : G → ℂ) g = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro f hf g hg
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, hf g hg, smul_zero]
  | ι x =>
    intro f hf g hg
    show (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f : G → ℂ) g = 0
    rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
    exact UpperTheory.ConvolutionTheory.Tf.deriv_zero h hU hf _ g hg
  | mul a b iha ihb =>
    intro f hf
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact iha _ (ihb f hf)
  | add a b iha ihb =>
    intro f hf g hg
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, iha f hf g hg,
      ihb f hf g hg, add_zero]

end

theorem UpperTheory.ConvolutionTheory.Tf.invSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (f : archGroup K n → ℂ), f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) →
      (fun g => f g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) ∧ Continuous f ∧ (HasCompactSupport f → (isExpLieAlgebra K n).IsTestFunction f) ∧
      ∀ (hf : f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (u : UEnv K n), tsupport ((isExpLieAlgebra K n).rightUAction u ⟨f, hf⟩ : archGroup K n → ℂ) ⊆ tsupport f := by
  intro K _ _ n f hf
  refine ⟨UpperTheory.ConvolutionTheory.Tf.smooth_inv _ hf, UpperTheory.ConvolutionTheory.Tf.smooth_cont _ hf, fun hc => ⟨hf, hc⟩, fun hf u => ?_⟩
  refine closure_minimal (fun g hg => ?_) (isClosed_tsupport f)
  by_contra hn
  exact hg (UpperTheory.ConvolutionTheory.Tf.act_zero _ (isClosed_tsupport f).isOpen_compl u ⟨f, hf⟩
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) g hn)

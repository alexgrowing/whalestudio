import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterC

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rUC_tmul (c : ℂ) (a : UEnv K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    rUC (c ⊗ₜ[ℝ] a) f = c • (isExpLieAlgebra K n).rightUAction a f := by
  exact congrArg (fun T : Module.End ℂ ((isExpLieAlgebra K n).smoothFuns (F := ℂ)) => T f)
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ _) (isExpLieAlgebra K n).rightUAction
      (fun c _ => Algebra.commute_algebraMap_left c _) c a)

private theorem tsupport_rUC (u : UC K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    tsupport (rUC u f : archGroup K n → ℂ) ⊆ tsupport (f : archGroup K n → ℂ) := by
  induction u using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, Submodule.coe_zero]
    simp
  | tmul c a =>
    rw [rUC_tmul, Submodule.coe_smul]
    refine subset_trans ?_ ((UpperTheory.ConvolutionTheory.Tf.invSmooth K n f f.2).2.2.2 f.2 a)
    exact tsupport_smul_subset_right (fun _ => c) _
  | add u v hu hv =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact (tsupport_add _ _).trans (Set.union_subset hu hv)

private theorem tsupport_inv_subset {f f' : archGroup K n → ℂ} (h : tsupport f ⊆ tsupport f') :
    tsupport (fun g => f g⁻¹) ⊆ tsupport (fun g => f' g⁻¹) := by
  have e : ∀ φ : archGroup K n → ℂ, tsupport (fun g => φ g⁻¹) = (Homeomorph.inv (archGroup K n)) ⁻¹' tsupport φ := by
    intro φ
    rw [tsupport, tsupport, Homeomorph.preimage_closure]
    rfl
  rw [e, e]
  exact Set.preimage_mono h

private theorem smooth_inv {β : TI K n} (hβ : SmoothT β) :
    (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
  (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1

private theorem tsupport_rightUniversal {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) :
    tsupport (fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) ⊆ tsupport β := by
  have := tsupport_inv_subset (tsupport_rUC u ⟨fun g => β g⁻¹, h⟩)
  simpa only [inv_inv] using this

private theorem lact_apply {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) (g : archGroup K n) :
    lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ := by
  have hc : Continuous (fun g : archGroup K n => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) :=
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ (rUC u ⟨fun g => β g⁻¹, h⟩).2).2.1.comp continuous_inv
  have hs : HasCompactSupport (fun g : archGroup K n => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) :=
    β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_rightUniversal h u)
  have H : ∃ (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (γ : TI K n),
      ∀ g, γ g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
    ⟨h, ⟨⟨_, hc⟩, hs⟩, fun _ => rfl⟩
  rw [lact, dif_pos H]
  exact H.choose_spec.choose_spec g

private theorem lact_smooth {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) : SmoothT (lact u β) := by
  have e : (fun g => lact u β g) = fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
    funext (lact_apply h u)
  rw [SmoothT, e]
  exact (isExpLieAlgebra K n).mem_smoothFuns.1
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ (rUC u ⟨fun g => β g⁻¹, h⟩).2).1

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Tf.lactSpec :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β → ∃ h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ),
      (∀ (u : UC K n) (g : archGroup K n), lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) ∧
      (∀ u, SmoothT (lact u β) ∧ tsupport (lact u β) ⊆ tsupport β) ∧ lact 1 β = β ∧
      (∀ u v, lact (u * v) β = lact u (lact v β) ∧ lact (u + v) β = lact u β + lact v β) ∧
      (∀ (c : ℂ) u, lact (c • u) β = c • lact u β ∧ lact u (c • β) = c • lact u β) ∧
      (∀ β', SmoothT β' → SmoothT (β + β') ∧ ∀ u, lact u (β + β') = lact u β + lact u β') ∧
      ∀ (a : UEnv K n) (g : archGroup K n), lact ((1 : ℂ) ⊗ₜ[ℝ] a) β g =
        ((isExpLieAlgebra K n).rightUAction a ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ := by
  intro K _ _ n β hβ
  have h := smooth_inv hβ
  refine ⟨h, lact_apply h, fun u => ⟨lact_smooth h u, ?_⟩, ?_, fun u v => ⟨?_, ?_⟩, fun c u => ⟨?_, ?_⟩,
    fun β' hβ' => ⟨?_, fun u => ?_⟩, fun a g => ?_⟩
  · have e : (lact u β : archGroup K n → ℂ) = fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
      funext (lact_apply h u)
    rw [e]
    exact tsupport_rightUniversal h u
  · ext g
    rw [lact_apply h, map_one, Module.End.one_apply]
    simp only [inv_inv]
  · ext g
    have h' := smooth_inv (lact_smooth h v)
    have e : (⟨fun g => lact v β g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        rUC v ⟨fun g => β g⁻¹, h⟩ :=
      Subtype.ext (funext fun x => by rw [← inv_inv x, ← lact_apply h v, inv_inv])
    rw [lact_apply h, lact_apply h', e, map_mul, Module.End.mul_apply]
  · ext g
    rw [CompactlySupportedContinuousMap.add_apply, lact_apply h, lact_apply h, lact_apply h, map_add,
      LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  · ext g
    rw [CompactlySupportedContinuousMap.smul_apply, lact_apply h, lact_apply h, map_smul,
      LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · ext g
    have h' : (fun g => (c • β) g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
      Submodule.smul_mem _ c h
    have e : (⟨fun g => (c • β) g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        c • ⟨fun g => β g⁻¹, h⟩ := rfl
    rw [CompactlySupportedContinuousMap.smul_apply, lact_apply h', lact_apply h, e, map_smul,
      Submodule.coe_smul, Pi.smul_apply]
  · exact (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.add_mem _
      ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ'))
  · ext g
    have h₂ := smooth_inv hβ'
    have h' : (fun g => (β + β') g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
      Submodule.add_mem _ h h₂
    have e : (⟨fun g => (β + β') g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        ⟨fun g => β g⁻¹, h⟩ + ⟨fun g => β' g⁻¹, h₂⟩ := rfl
    rw [CompactlySupportedContinuousMap.add_apply, lact_apply h', lact_apply h, lact_apply h₂, e, map_add,
      Submodule.coe_add, Pi.add_apply]
  · rw [lact_apply h, rUC_tmul, one_smul]

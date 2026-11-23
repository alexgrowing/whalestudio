import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfAdicCompletionTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocalizationAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientFlatOfCompletionFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulRegularTensorOfQuotientFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfLocalizationFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationProjectiveKernelFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionFlatKernelFiniteStatement

open TensorProduct

namespace GlobalTheory.CompletionDescent

theorem finite_projective : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M], IsSMulRegular A f → IsSMulRegular M f → Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) → Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) → Module.Finite (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) → Module.Projective (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) → Module.Finite A M ∧ Module.Projective A M := by
  intro A _ f M _ _ hA hM hfl hpl hfc hpc
  have hfin : Module.Finite A M := GlobalTheory.T.finite_of_localization_and_completion A f (GlobalTheory.T.subsingleton_of_adic_completion_tensor A f) M hfl hfc
  have hflat : Module.Flat A M := by
    have h3 := GlobalTheory.T.quotient_flat_of_completion_flat A f M inferInstance
    rw [Module.Flat.iff_rTensor_injective']
    intro I
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨k, hk⟩ := GlobalTheory.T.torsion_of_localization_flat A f M inferInstance I y hy
    have hI : IsSMulRegular I f := fun a b h => Subtype.ext (hA (congrArg Subtype.val h))
    have hreg := GlobalTheory.T.smul_regular_tensor_of_quotient_flat A f M hM h3 I hI
    exact (hreg.pow k) (show f ^ k • y = f ^ k • (0 : TensorProduct A I M) by rw [hk, smul_zero])
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  have hK : Module.Finite A (LinearMap.ker π) :=
    GlobalTheory.T.finite_of_localization_and_completion A f (GlobalTheory.T.subsingleton_of_adic_completion_tensor A f) _ (GlobalTheory.T.localization_projective_kernel_finite A f M hpl n π hπ)
      (GlobalTheory.T.completion_flat_kernel_finite A f M hflat hpc n π hπ)
  have : Module.FinitePresentation A M :=
    Module.finitePresentation_of_surjective π hπ (Module.Finite.iff_fg.mp hK)
  exact ⟨hfin, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.CompletionDescent

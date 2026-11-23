import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

open PiTensorProduct

theorem piTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  intro α _ _ Γ _ X Y _ _ _ _ ρ ρ' h
  choose S f hf using h
  let ι : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ') :=
    { toLinearMap := PiTensorProduct.map fun a => (S a).toSubmodule.subtype
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        rfl }
  let π : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ) :=
    { toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        congr 1
        funext a
        exact (f a).isIntertwining _ _ (g a) (x a) }
  have hι : Function.Injective ι := by
    choose r hr using fun a => LinearMap.exists_leftInverse_of_injective (S a).toSubmodule.subtype
      (S a).toSubmodule.ker_subtype
    have : (PiTensorProduct.map r) ∘ₗ (PiTensorProduct.map fun a => (S a).toSubmodule.subtype)
        = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hr]
      exact PiTensorProduct.map_id
    exact Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => LinearMap.congr_fun this z
  have hπ : Function.Surjective π := by
    show Function.Surjective (PiTensorProduct.map fun a => (f a).toLinearMap)
    rw [← LinearMap.range_eq_top]
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    choose y hy using fun a => hf a (x a)
    exact ⟨PiTensorProduct.tprod ℂ y, by
      show PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext a
      exact hy a⟩
  exact (IsSubquotient.of_surjective π hπ).trans (IsSubquotient.of_injective ι hι)

end GlobalTheory

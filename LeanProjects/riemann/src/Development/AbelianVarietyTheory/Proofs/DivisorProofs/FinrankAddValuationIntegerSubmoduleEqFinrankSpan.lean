import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem finrank_addValuationInteger_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X →
    finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) =>
      (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  intro C _ v N X hX
  let ι : (Fin N → Int0 v) →ₗ[Int0 v] (Fin N → C) := (Algebra.linearMap (Int0 v) C).compLeft (Fin N)
  have hι : Function.Injective ι := by
    intro x y h; funext i; exact Subtype.ext (congrFun h i)
  let L : X →ₗ[Int0 v] (Fin N → C) := ι ∘ₗ X.subtype
  have hL : Function.Injective L := hι.comp Subtype.val_injective
  haveI : Module.IsTorsionFree (Int0 v) X := inferInstance
  haveI : Module.Free (Int0 v) X := free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  let b := Module.Free.chooseBasis (Int0 v) X
  have hli : LinearIndependent (Int0 v) (L ∘ b) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hliC : LinearIndependent C (L ∘ b) := (LinearIndependent.iff_fractionRing (Int0 v) C).mp hli
  have hspan : Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (X : Set (Fin N → Int0 v))) = Submodule.span C (Set.range (L ∘ b)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : L ⟨x, hx⟩ ∈ Submodule.span (Int0 v) (L '' Set.range b) :=
        Submodule.apply_mem_span_image_of_mem_span L (by rw [b.span_eq]; trivial)
      rw [← Set.range_comp] at h1
      exact Submodule.span_le_restrictScalars (Int0 v) C _ h1
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(b k : Fin N → Int0 v), (b k).2, rfl⟩
  rw [hspan, finrank_span_eq_card hliC, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory

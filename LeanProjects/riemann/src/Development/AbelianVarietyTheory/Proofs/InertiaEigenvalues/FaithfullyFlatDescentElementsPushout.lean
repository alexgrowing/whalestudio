import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ff_descent_elem_pushout : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), f.FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → Function.Injective f ∧ ∀ b, p b = q b → b ∈ f.range := by
  intro A B D _ _ _ f p q hf hpo
  refine ⟨hf.injective, fun b hb => ?_⟩
  letI : Algebra A B := f.toAlgebra
  haveI : Module.FaithfullyFlat A B := hf

  have hw : CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B))) =
      CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom) := by
    ext a
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := B) a
  have e := congrArg (fun x => (hpo.desc _ _ hw).hom x) hb
  have e1 := congrArg (fun g => g.hom b) (hpo.inl_desc _ _ hw)
  have e2 := congrArg (fun g => g.hom b) (hpo.inr_desc _ _ hw)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e e1 e2

  have key : b ∈ (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B)).eqLocus
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom :=
    e1.symm.trans (e.trans e2)
  have hmem := (Algebra.IsEffective.of_faithfullyFlat A B).eqLocus_includeLeft_includeRight ▸
    SetLike.mem_coe.mpr key
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

end GlobalTheory.BSP

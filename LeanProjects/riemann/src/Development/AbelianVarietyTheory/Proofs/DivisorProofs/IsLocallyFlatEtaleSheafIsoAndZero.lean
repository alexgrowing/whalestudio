import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem flatS_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  intro R _
  refine ⟨?_, ?_⟩
  · intro M N e ⟨P, φ, hs, hi, hf⟩
    refine ⟨P, φ ≫ e.hom.hom, ?_, ?_, hf⟩
    · intro U y
      obtain ⟨S, hS, hy⟩ := hs U (Sec.map e.inv y)
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hy V g hg
      refine ⟨x, ?_⟩
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hx]
      have h1 := congrArg ModuleCat.Hom.hom (e.hom.hom.naturality g.op)
      have h2 := congrArg (fun (f : N ⟶ N) => (f.hom.app (op U)).hom y) e.inv_hom_id
      simp only [ModuleCat.hom_comp] at h1
      have h3 := LinearMap.congr_fun h1 ((e.inv.hom.app (op U)).hom y)
      simp only [LinearMap.comp_apply] at h3
      simp only [Sec.res, Sec.map]
      rw [h3]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      rw [h2]
    · intro U x hx
      apply hi U x
      have h2 := congrArg (fun (f : M ⟶ M) => (f.hom.app (op U)).hom ((φ.app (op U)).hom x)) e.hom_inv_id
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      rw [← h2, hx, map_zero]
  · intro M hM
    refine ⟨(Functor.const _).obj (ModuleCat.of (ULift.{1} R) PUnit.{2}), 0, ?_, ?_, ?_⟩
    · intro U y
      refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨0, ?_⟩⟩
      have h := congrArg (fun (f : M ⟶ M) => (f.hom.app (op V)).hom (Sec.res g y)) (hM.eq_of_src (𝟙 M) 0)
      simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h
      rw [h]
      simp
    · intro U x _
      exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ => Subsingleton.elim (α := PUnit.{2}) _ _⟩
    · intro U _
      show Module.Flat (ULift.{1} R) PUnit.{2}
      infer_instance

end GlobalTheory.EtC

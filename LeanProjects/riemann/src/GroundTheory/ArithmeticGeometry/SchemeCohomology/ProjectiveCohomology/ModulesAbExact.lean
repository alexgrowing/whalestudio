import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

theorem epi_toSheaf_map {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N) [Epi φ] :
    Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (J := Opens.grothendieckTopology X) (𝟙 X.ringCatSheaf.obj)
  let a := PresheafOfModules.sheafification (J := Opens.grothendieckTopology X)
    (𝟙 X.ringCatSheaf.obj)
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let φ₀ := G.map φ
  have hnat : a.map φ₀ ≫ adj.counit.app N = adj.counit.app M ≫ φ := adj.counit.naturality φ
  have h₁ : Epi (a.map φ₀) := by
    have : a.map φ₀ = adj.counit.app M ≫ φ ≫ inv (adj.counit.app N) := by
      rw [← reassoc_of% hnat, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  have hfac : a.map φ₀ = a.map (factorThruImage φ₀) ≫ a.map (image.ι φ₀) := by
    rw [← a.map_comp, image.fac]
  have h₂ : Epi (a.map (image.ι φ₀)) := by
    rw [hfac] at h₁
    exact epi_of_epi (a.map (factorThruImage φ₀)) _
  have h₃ : IsIso (a.map (image.ι φ₀)) := isIso_of_mono_of_epi _
  have h₄ : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map (a.map φ₀)) := by
    rw [hfac, Functor.map_comp]
    have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map (a.map (factorThruImage φ₀))) := by
      have e₁ : Epi ((PresheafOfModules.toPresheaf _).map (factorThruImage φ₀)) := by
        apply NatTrans.epi_of_epi_app
      change Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map (factorThruImage φ₀)))
      exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_epi _
    infer_instance
  have : (SheafOfModules.toSheaf X.ringCatSheaf).map φ =
      inv ((SheafOfModules.toSheaf X.ringCatSheaf).map (adj.counit.app M)) ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map (a.map φ₀) ≫
          (SheafOfModules.toSheaf X.ringCatSheaf).map (adj.counit.app N) := by
    rw [← Functor.map_comp, hnat, Functor.map_comp, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

theorem epi_modulesAbMap {F G : X.Modules} (φ : F ⟶ G) [hφ : Epi φ] : Epi (modulesAbMap φ) :=
  @epi_toSheaf_map X F G φ hφ

def abShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (modulesAbMap S.f) (modulesAbMap S.g) (by
    rw [← modulesAbMap_comp, S.zero]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero _ _)

theorem shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}
    (hS : S.ShortExact) : (S.map (SheafOfModules.toSheaf X.ringCatSheaf)).ShortExact := by
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.toSheaf X.ringCatSheaf)).1 inferInstance S hS
  have := h.2
  have := hS.epi_g
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g) := epi_toSheaf_map S.g
  exact ShortComplex.ShortExact.mk' h.1 (by assumption) (by assumption)

theorem shortExact_abShortComplex {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (abShortComplex S).ShortExact :=
  shortExact_map_toSheaf (S := S) hS

end

end GroundTheory.Arith.SchemeCoh

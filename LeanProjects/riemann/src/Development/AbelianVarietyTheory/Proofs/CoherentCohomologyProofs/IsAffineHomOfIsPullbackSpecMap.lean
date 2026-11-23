import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Base

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

theorem baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_SpecMap {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm

abbrev baseModule (p : X ⟶ Spec R) (F : X.Modules) (U : X.Opens) : Module R Γ(F, U) :=
  Module.compHom Γ(F, U) (baseRingHom p U).hom

def appLinearBase (p : X ⟶ Spec R) (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) :
    letI := baseModule p F U
    letI := baseModule (g ≫ p) G (g ⁻¹ᵁ U)
    Γ(F, U) →ₗ[R] Γ(G, g ⁻¹ᵁ U) :=
  letI := baseModule p F U
  letI := baseModule (g ≫ p) G (g ⁻¹ᵁ U)
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ (φ.app_smul _ s).trans
      congr($(app_baseRingHom g p U r) • (show Γ(G, g ⁻¹ᵁ U) from φ.app U s)) }

@[simp]
theorem appLinearBase_apply (p : X ⟶ Spec R) (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) (s : Γ(F, U)) :
    appLinearBase p g φ U s = φ.app U s := rfl

def appLinearPreimage (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) :
    letI := Module.compHom Γ(G, g ⁻¹ᵁ U) (g.app U).hom
    Γ(F, U) →ₗ[Γ(X, U)] Γ(G, g ⁻¹ᵁ U) :=
  letI := Module.compHom Γ(G, g ⁻¹ᵁ U) (g.app U).hom
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ φ.app_smul r s }

end Base

section Localization

variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))

include H

omit S in
theorem baseRingHom_algebraMap (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by
  rw [H.w, baseRingHom_comp_SpecMap]; rfl

omit S in
theorem isAffineHom_of_isPullback_SpecMap : IsAffineHom g :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance

theorem isLocalization_app {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (g.app V).hom.toAlgebra
    IsLocalization (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have po' : IsPushout (baseRingHom p V) (CommRingCat.ofHom (algebraMap R L)) (g.app V)
      (baseRingHom q (g ⁻¹ᵁ V)) := by
    refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (g.app V).hom.toAlgebra
  let := (baseRingHom p V).hom.toAlgebra
  let := (baseRingHom q (g ⁻¹ᵁ V)).hom.toAlgebra
  let := (baseRingHom (g ≫ p) (g ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom g p V r).symm
  have : IsScalarTower R L Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap H _ r).symm
  exact (Algebra.isLocalization_iff_isPushout S L).mpr
    (CommRingCat.isPushout_iff_isPushout.mp po')

end Localization

end GlobalTheory.QCoh.Qcqs

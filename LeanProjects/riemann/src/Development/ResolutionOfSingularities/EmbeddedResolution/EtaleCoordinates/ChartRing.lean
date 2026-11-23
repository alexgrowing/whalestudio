import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comp_presheafMap_comp_presheafMap {X₁ : Scheme.{u}} {R : CommRingCat.{u}}
    {A B C : (X₁.Opens)ᵒᵖ} (h : R ⟶ X₁.presheaf.obj A) (g₁ : A ⟶ B) (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    (h ≫ X₁.presheaf.map g₁) ≫ X₁.presheaf.map g₂ = h ≫ X₁.presheaf.map g₃ := by
  rw [Category.assoc, ← Functor.map_comp, Scheme.presheaf_map_eq_of_parallel X₁ (g₁ ≫ g₂) g₃]

private theorem appTop_comp_topIso_hom {X₁ Y₁ : Scheme.{u}} (f : X₁ ⟶ Y₁) (V : X₁.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y₁.Opens)) :
    (V.ι ≫ f).appTop ≫ V.topIso.hom = f.appLE ⊤ V hV := by
  have hR : f.appLE ⊤ V hV = f.app ⊤ ≫ X₁.presheaf.map (homOfLE hV).op := rfl
  simp
  rw [hR]
  exact comp_presheafMap_comp_presheafMap _ _ _ _

theorem appLE_top_comp_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ V hV ≫ V.topIso.inv = (V.ι ≫ f).appTop := by
  rw [← appTop_comp_topIso_hom f V hV, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def affineSpaceGlobalSectionsHom (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(affineSpaceFin k m, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

def EtaleChart.coord (c : EtaleChart p U m) (j : Fin m) : Γ(X, U) :=
  U.topIso.hom.hom
    (c.map.appTop.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))))

theorem EtaleChart.coord_def (c : EtaleChart p U m) (j : Fin m) :
    c.coord j =
      U.topIso.hom.hom
        (c.map.appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) :=
  rfl

def EtaleChart.coordRingHom (c : EtaleChart p U m) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U) :=
  (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m)

theorem EtaleChart.coordRingHom_def (c : EtaleChart p U m) :
    c.coordRingHom = (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m) :=
  rfl

private theorem appTop_hom_appTop_inv_apply {A B : Scheme.{u}} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (Scheme.Hom.appTop e.hom).hom ((Scheme.Hom.appTop e.inv).hom x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom = 𝟙 Γ(A, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  have h2 := congrArg (fun f : Γ(A, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom f x) h
  simpa using h2

private theorem affineSpace_specIso_inv_appTop_coord (K : Type u) [Field K] (n : ℕ) (j : Fin n) :
    ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)))
      = ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom
          (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n))) := by
  exact AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of K) (ULift.up j)

private theorem affineSpaceGlobalSectionsHom_X (K : Type u) [Field K] (n : ℕ) (j : Fin n) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n)))
      = AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)) := by
  simp only [affineSpaceGlobalSectionsHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← affineSpace_specIso_inv_appTop_coord K n j]
  exact appTop_hom_appTop_inv_apply _ _

@[simp] theorem EtaleChart.coordRingHom_X (c : EtaleChart p U m) (j : Fin m) :
    c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j := by
  rw [EtaleChart.coordRingHom_def, EtaleChart.coord_def]
  simp only [RingHom.comp_apply, affineSpaceGlobalSectionsHom_X]

private theorem affineSpace_specIso_hom_comp_specMap_C (K : Type u) [Field K] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) =
      affineSpaceFinToSpec K n := by
  have h : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv ≫
      affineSpaceFinToSpec K n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) := by
    simp
  rw [← h, Iso.hom_inv_id_assoc]

theorem EtaleChart.coordRingHom_comp_C (c : EtaleChart p U m) :
    c.coordRingHom.comp (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) =
      sectionsAlgebraMap k p U := by
  have hC : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop ≫
            c.map.appTop ≫ U.topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U) := by
    rw [← Category.assoc, hC, Category.assoc,
      ← Category.assoc _ _ (c.map.appTop ≫ U.topIso.hom), ← Scheme.Hom.comp_appTop,
      affineSpace_specIso_hom_comp_specMap_C k m, ← Category.assoc _ _ U.topIso.hom,
      ← Scheme.Hom.comp_appTop, c.comp_struct, appTop_comp_topIso_hom p U (le_preimage_top k p U)]
  have h := congrArg CommRingCat.Hom.hom key
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem EtaleChart.coordRingHom_C (c : EtaleChart p U m) (a : k) :
    c.coordRingHom (MvPolynomial.C a) = sectionsAlgebraMap k p U a :=
  DFunLike.congr_fun (EtaleChart.coordRingHom_comp_C c) a

theorem EtaleChart.coordRingHom_etale (c : EtaleChart p U m) (hU : IsAffineOpen U) :
    c.coordRingHom.Etale := by
  have hUaff : IsAffine U.toScheme := hU
  have hEt : AlgebraicGeometry.Etale c.map := c.isEtale
  have hAaff : IsAffine (affineSpaceFin k m) := inferInstance
  have hbeta : IsIso (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom) :=
    inferInstanceAs (IsIso
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.app ⊤))
  have hResp : RingHom.RespectsIso @RingHom.Etale := RingHom.Etale.respectsIso
  have hmap : RingHom.Etale (Scheme.Hom.appTop c.map).hom :=
    AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine.mp c.isEtale
  exact (hResp.cancel_left_isIso
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv)
      (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom ≫
        Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
    ((hResp.cancel_left_isIso
        (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom)
        (Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
      ((hResp.cancel_right_isIso (Scheme.Hom.appTop c.map) U.topIso.hom).mpr hmap))

@[reducible] def EtaleChart.algebra (c : EtaleChart p U m) :
    Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
  c.coordRingHom.toAlgebra

theorem EtaleChart.algebraMap_eq_coordRingHom (c : EtaleChart p U m) :
    @algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra = c.coordRingHom :=
  rfl

theorem EtaleChart.algebra_etale (c : EtaleChart p U m) (hU : IsAffineOpen U) :
    @Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra := by
  have h : c.coordRingHom.Etale := EtaleChart.coordRingHom_etale c hU
  exact h

theorem EtaleChart.algebra_formallyEtale (c : EtaleChart p U m) (hU : IsAffineOpen U) :
    @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra := by
  have h := EtaleChart.algebra_etale c hU
  exact h.1

theorem EtaleChart.isScalarTower (c : EtaleChart p U m) :
    @IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
      (@Algebra.toSMul k (MvPolynomial (ULift.{u} (Fin m)) k) _ _ _)
      (@Algebra.toSMul (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra)
      (@Algebra.toSMul k Γ(X, U) _ _ (sectionsAlgebra k p U)) := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instBase : Algebra k Γ(X, U) := sectionsAlgebra k p U
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (EtaleChart.coordRingHom_C c x).symm

private theorem ideal_map_topIso_inv_injective {X₁ : Scheme.{u}} (V : X₁.Opens)
    {J₁ J₂ : Ideal Γ(X₁, V)}
    (hJ : Ideal.map V.topIso.inv.hom J₁ = Ideal.map V.topIso.inv.hom J₂) : J₁ = J₂ := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    ext x
    exact Iso.inv_hom_id_apply V.topIso x
  have key : ∀ J : Ideal Γ(X₁, V),
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [← key J₁, hJ, key J₂]

private theorem ι_appLE_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel X₁ _ _

theorem EtaleChart.ideal_eq_span_coord (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (I : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal I U = c.coordIdeal S) :
    I.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) := by
  have hUaff : IsAffine U.toScheme := hU
  have e : (⊤ : (U.toScheme).Opens) ≤ U.ι ⁻¹ᵁ U := by
    intro x _
    exact x.2
  have hL : (restrictIdeal I U).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩) := by
    rw [restrictIdeal_eq_comap_ι, ← ι_appLE_top_eq_topIso_inv U e]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U, hU⟩
      ⟨⊤, isAffineOpen_top U.toScheme⟩ e
  have hR : (c.coordIdeal S).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
      coordSubspaceIdeal_eq_ofIdealTop_span_coord, AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top,
      Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
    refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
    exact (Iso.hom_inv_id_apply U.topIso _).symm
  have hfin : Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩)
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [← hL, ← hR, h]
  exact ideal_map_topIso_inv_injective U hfin

theorem EtaleChart.etaleCoordinates_coord (c : EtaleChart p U m) (j : Fin m) :
    @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c.algebra
      (ULift.up j : ULift.{u} (Fin m)) = c.coord j := by
  have h : c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j :=
    EtaleChart.coordRingHom_X c j
  exact h

end FunctorialResolution.EmbeddedResolution

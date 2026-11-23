import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem eq_ptMap' {O : Type} [CommRing O] {D B : Type} [CommRing D] [Algebra O D] [CommRing B] [Algebra O B]
    (x : specO O D ⟶ specO O B) : ∃ α : B →ₐ[O] D, x = ptMap α := by
  obtain ⟨f, hf⟩ := Spec.map_surjective x.left
  have hw : x.left ≫ (specO O B).hom = (specO O D).hom := Over.w x
  rw [← hf] at hw
  change Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) = Spec.map (CommRingCat.ofHom (algebraMap O D)) at hw
  rw [← Spec.map_comp] at hw
  have hc := Spec.map_injective hw
  refine ⟨{ f.hom with commutes' := fun c => congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of D => g.hom c) hc }, ?_⟩
  ext1
  rw [← hf]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

theorem at_ptMap {D : Type} [CommRing D] [Algebra O D] (α : Bt P' x0 hu →ₐ[O] D)
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    P'.At ((algebraMap O D).comp x0) ((ptMap α ≫ aH P' x0 hu hπ).left ≫ π) (α.toRingHom.comp (inB P' x0 hu)) := by
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_assoc, inB_str]
    exact RingHom.ext fun r => α.commutes (x0 r)
  · rw [Over.comp_left, Category.assoc, aH_left_π]
    change spMap _ ≫ P'.u.left = spMap α.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm

theorem unitOf_ptMap_chi {D : Type} [CommRing D] [Algebra O D] (α : Bt P' x0 hu →ₐ[O] D) (b : P'.Bˣ) :
    (unitOf (ptMap α ≫ chi P' x0 hu b) : D) = α (inB P' x0 hu b) := by
  rw [GlobalTheory.GmPoints.unitOf_ptMap, unitOf_chi]
  rfl

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

theorem chi_mul_aff (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ}
    {b : P'.Bˣ} (hb : P'.Gl κ b) {D : Type} [CommRing D] [Algebra O D] (x y z : specO O D ⟶ Hs P' x0 hu)
    (h : z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1)) :
    z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  obtain ⟨αx, rfl⟩ := eq_ptMap' x
  obtain ⟨αy, rfl⟩ := eq_ptMap' y
  obtain ⟨αz, rfl⟩ := eq_ptMap' z
  have hw : ∀ α : Bt P' x0 hu →ₐ[O] D,
      ((ptMap α ≫ aH P' x0 hu hg.1).left ≫ π) ≫ t.G.hom = (specO O D).hom ≫ spMap x0 ≫ ξ := fun α => by
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w]
  let w : (Bt P' x0 hu →ₐ[O] D) → (Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G) := fun α =>
    Over.homMk _ (hw α)
  have hm := hg.2 (specO O D) (ptMap αx ≫ aH P' x0 hu hg.1) (ptMap αy ≫ aH P' x0 hu hg.1) (w αx) (w αy) rfl rfl
  rw [← h] at hm
  have hz : P'.At ((algebraMap O D).comp x0) (w αx * w αy).left (αz.toRingHom.comp (inB P' x0 hu)) := by
    rw [hm]; exact at_ptMap P' x0 hu αz hg.1
  have e := hb.2 D _ _ (w αx) (w αy) _ _ _ (at_ptMap P' x0 hu αx hg.1) (at_ptMap P' x0 hu αy hg.1) hz
  apply GlobalTheory.GmPoints.unitOf_bijective.1
  rw [GlobalTheory.GmPoints.unitOf_mul]
  ext1
  rw [Units.val_mul, unitOf_ptMap_chi, unitOf_ptMap_chi, unitOf_ptMap_chi]
  exact e

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.chi_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b → ∀ (S : Over (Sp O)) (x y z : S ⟶ Hs P' x0 hu), z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) → z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg κ b hb S x y z h
  have loc : ∀ (R' : CommRingCat.{0}) (f : Spec R' ⟶ S.left),
      f ≫ (z ≫ chi P' x0 hu b).left = f ≫ ((x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b)).left := by
    intro R' f
    letI : Algebra O R' := (Spec.preimage (f ≫ S.hom)).hom.toAlgebra
    let c : specO O R' ⟶ S := Over.homMk f (by
      change f ≫ S.hom = Spec.map (CommRingCat.ofHom (Spec.preimage (f ≫ S.hom)).hom)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage])
    have h' : (c ≫ z) ≫ aH P' x0 hu hg.1 = ((c ≫ x) ≫ aH P' x0 hu hg.1) * ((c ≫ y) ≫ aH P' x0 hu hg.1) := by
      rw [Category.assoc, h, MonObj.comp_mul, Category.assoc, Category.assoc]
    have k := GlobalTheory.FinPartAt.chi_mul_aff P' x0 hu hg hb _ _ _ h'
    rw [Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul] at k
    exact congrArg CommaMorphism.left k
  exact Over.OverMorphism.ext (S.left.affineCover.hom_ext _ _ fun i => loc _ _)

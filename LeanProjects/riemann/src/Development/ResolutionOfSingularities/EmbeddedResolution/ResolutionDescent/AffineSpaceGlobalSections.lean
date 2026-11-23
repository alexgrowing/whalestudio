import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIsoSpecMvPolynomial (k : Type u) [Field k] (v : Type u) :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v (CommRingCat.of k)

def mvPolynomialToGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv).hom

def globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom

private theorem appTop_inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  simp

private theorem appTop_hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
  simp

private theorem mvPolynomialToGlobalSections_apply (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

private theorem globalSectionsToMvPolynomial_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    globalSectionsToMvPolynomial k v s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

theorem leftInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.LeftInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro p
  rw [mvPolynomialToGlobalSections_apply, globalSectionsToMvPolynomial_apply, appTop_inv_hom_apply]
  simp

theorem rightInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.RightInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro s
  rw [globalSectionsToMvPolynomial_apply, mvPolynomialToGlobalSections_apply, Iso.hom_inv_id_apply,
    appTop_hom_inv_apply]

def mvPolynomialEquivGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := leftInverse_globalSectionsToMvPolynomial k v
  right_inv := rightInverse_globalSectionsToMvPolynomial k v
  map_mul' := map_mul (mvPolynomialToGlobalSections k v)
  map_add' := map_add (mvPolynomialToGlobalSections k v)

theorem mvPolynomialEquivGlobalSections_apply (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    mvPolynomialEquivGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

theorem mvPolynomialEquivGlobalSections_symm_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

private theorem affineSpaceIsoSpecMvPolynomial_inv_appTop_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.X i) := by
  rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]

@[simp]
theorem mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [mvPolynomialEquivGlobalSections_apply, ← affineSpaceIsoSpecMvPolynomial_inv_appTop_coord k v i, appTop_hom_inv_apply]

@[simp]
theorem mvPolynomialEquivGlobalSections_symm_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      MvPolynomial.X i := by
  rw [← mvPolynomialEquivGlobalSections_X k v i, RingEquiv.symm_apply_apply]

theorem mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (v : Type u) (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have h2 : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      ((affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.C c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp
    rw [← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
    simp
  rw [← key, appTop_hom_inv_apply]

theorem mvPolynomialEquivGlobalSections_basicOpen (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, Scheme.preimage_basicOpen]
  rfl

theorem mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]

end FunctorialResolution.EmbeddedResolution

end

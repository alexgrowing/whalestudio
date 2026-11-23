import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_affineOpen_of_isAffine {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens) :
    (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  haveI : IsAffine (W.1 : Scheme) := W.2
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (K.comap f) W.1.ι
    ⟨⊤, isAffineOpen_top _⟩
  rw [← Scheme.IdealSheafData.comap_comp, IdealSheafData.ideal_comap_top_of_isAffine] at h1
  have hc : (W.1.ι ≫ f).appTop ≫ (W.1.ι.appIso ⊤).inv = f.appLE ⊤ (W.1.ι ''ᵁ ⊤) (by simp) := by
    simp [Scheme.Hom.appLE]; exact Category.comp_id _
  have hs : Function.Surjective (W.1.ι.appIso ⊤).inv.hom :=
    (W.1.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective
  have h2 : (K.comap f).ideal ⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ =
      Ideal.map (f.appLE ⊤ (Subtype.val (⟨W.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens)) (by simp)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rw [← hc, CommRingCat.hom_comp, ← Ideal.map_map, h1, Ideal.map_comap_of_surjective _ hs]
  have hW : (⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  have key : ∀ V : X.affineOpens, V = W →
      (K.comap f).ideal V = Ideal.map (f.appLE ⊤ V.1 (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) →
      (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rintro V rfl h; exact h
  exact key _ hW h2

example : ∀ {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens), (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
  fun f K W => IdealSheafData.ideal_comap_affineOpen_of_isAffine f K W

end GlobalTheory

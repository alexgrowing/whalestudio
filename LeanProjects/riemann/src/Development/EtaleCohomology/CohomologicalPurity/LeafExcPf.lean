import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem freeSq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) (p : SimplexCategoryᵒᵖ) :
    (free R).map (P'.hom.app p) ≫ (free R).map (φ.right.app p) =
      (free R).map (φ.left.app p) ≫ (free R).map (P.hom.app p) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, Arrow.w φ]

def LeafExcFormal : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → Exc q φ

theorem freeSqSch (R : Type) [CommRing R] {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) :
    (free R).map (yoneda.map U'.ι) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (f.resLE U U' h)) ≫ (free R).map (yoneda.map U.ι) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]

def LeafExcSheaf : Prop := ∀ (R : Type) [CommRing R] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X')
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens),
  (U : Set X) = (Set.range ι)ᶜ → ∀ h : U' = f ⁻¹ᵁ U,
  IsIso (cokernel.map ((free R).map (yoneda.map U'.ι)) ((free R).map (yoneda.map U.ι))
    ((free R).map (yoneda.map (f.resLE U U' h.le))) ((free R).map (yoneda.map f)) (freeSqSch R f U' U h.le))

theorem LeafExc_of (hF : LeafExcFormal) (hS : LeafExcSheaf) : LeafExc := by
  intro _ q X' X Z f _ ι' ι _ hp U' U hU h
  refine hF q _ fun p => ?_
  exact hS (ZMod q) f ι' ι hp U' U hU h

end LateralTheory.CohomologicalPurity

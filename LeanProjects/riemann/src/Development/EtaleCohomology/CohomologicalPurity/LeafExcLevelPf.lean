import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def MM {P' P : Arrow Spc} (φ : P' ⟶ P) : Spc := pushout P'.hom (P'.hom ≫ φ.right)

def gM {P' P : Arrow Spc} (φ : P' ⟶ P) : MM φ ⟶ dbl P :=
  pushout.desc (φ.right ≫ dbl.inl P) (dbl.inr P) (by
    rw [← Category.assoc, ← Arrow.w φ, Category.assoc, Category.assoc]
    exact congrArg (φ.left ≫ ·) (pushout.condition (f := P.hom) (g := P.hom)))

def LeafExcOfEqv : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ i, Eqv (ZMod q) (gM φ) (tw q i)) → Exc q φ

def LeafEqvOfExc : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), Exc q φ → ∀ i, Eqv (ZMod q) (gM φ) (tw q i)

def LeafMLev : Prop := ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (n : SimplexCategoryᵒᵖ),
  ∃ (a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ)) (b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P)),
    disc.map ((gM φ).app n) ≫ b.hom = a.hom ≫ gM ((lev n).map φ)

theorem LeafExcLevel_of (h1 : LeafExcOfEqv) (h2 : LeafEqvOfExc) (h3 : LeafMLev) : LeafExcLevel := by
  intro a3 q P' P φ hl
  apply h1 q P' P φ
  intro i
  apply a3
  intro n
  obtain ⟨a, b, w⟩ := h3 P' P φ n
  have e : disc.map ((gM φ).app n) = a.hom ≫ gM ((lev n).map φ) ≫ b.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact eqv_comp (eqv_iso _ _) (eqv_comp (h2 q _ _ _ (hl n) i) (eqv_iso _ _))

end LateralTheory.CohomologicalPurity.TubeCut

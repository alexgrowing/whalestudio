import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := ⟨G.obj e.1, (α.app e.1).app U e.2⟩
  map {e e'} g := ⟨G.map g.1, by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.1) U) e.2
    have h2 : (D'.map g.1).app U e.2 = e'.2 := g.2
    exact h.symm.trans (congrArg (fun y => (α.app e'.1).app U y) h2)⟩
  map_id e := Subtype.ext (G.map_id e.1)
  map_comp g g' := Subtype.ext (G.map_comp g.1 g'.1)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ CategoryOfElements.π F = B ⋙ CategoryOfElements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (CategoryOfElements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ CategoryOfElements.map (D.flip.map f) = CategoryOfElements.map (D'.flip.map f) ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    have h := ConcreteCategory.congr_hom ((α.app e.1).naturality f) e.2
    exact Sigma.ext rfl (heq_of_eq h.symm)) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ CategoryOfElements.map (D'.flip.map f)) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ CategoryOfElements.map (D.flip.map f)
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).1) U) ((chn x).obj 0).2

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut

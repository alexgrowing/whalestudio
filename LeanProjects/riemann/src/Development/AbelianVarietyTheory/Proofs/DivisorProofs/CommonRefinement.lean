import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

structure CommonRef {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C']
    (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X) : Type where

  t : C

  t' : C'

  W : X.affineOpens
  le : W.1 ≤ opOf G t
  le' : W.1 ≤ opOf G' t'

namespace CommonRef

variable {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C']
  {G : C ⥤ AffOp X} {G' : C' ⥤ AffOp X}

instance : Category.{0} (CommonRef G G') where
  Hom a b := (a.t ⟶ b.t) × (a.t' ⟶ b.t') × PLift (b.W.1 ≤ a.W.1)
  id a := (𝟙 _, 𝟙 _, ⟨le_rfl⟩)
  comp f g := (f.1 ≫ g.1, f.2.1 ≫ g.2.1, ⟨g.2.2.down.trans f.2.2.down⟩)
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance : Quiver.IsThin (CommonRef G G') := fun a b =>
  ⟨fun f g => Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

variable (G G')

def fst : CommonRef G G' ⥤ C where
  obj d := d.t
  map f := f.1

def snd : CommonRef G G' ⥤ C' where
  obj d := d.t'
  map f := f.2.1

def opn : CommonRef G G' ⥤ AffOp X where
  obj d := Opposite.op d.W
  map f := (homOfLE f.2.2.down).op

def toFst : fst G G' ⋙ G ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G.obj d.t).unop from d.le)).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def toSnd : snd G G' ⋙ G' ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G'.obj d.t').unop from d.le')).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem isBas (hG : IsBas (opOf G)) (hG' : IsBas (opOf G')) : IsBas (opOf (opn G G')) := by
  refine ⟨fun x U hx => ?_, fun d₁ d₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨t, hxt, htU⟩ := hG.1 x U hx
    obtain ⟨t', hxt', ht'⟩ := hG'.1 x (opOf G t ⊓ U) ⟨hxt, hx⟩
    exact ⟨⟨t, t', (G'.obj t').unop, ht'.trans inf_le_left, le_rfl⟩, hxt', ht'.trans inf_le_right⟩
  · have hx₃ : x ∈ U ⊓ d₁.W.1 ⊓ d₂.W.1 := ⟨⟨hx, h₁⟩, h₂⟩
    obtain ⟨t, a₁, a₂, hxt, htU⟩ := hG.2 d₁.t d₂.t x _ hx₃ (d₁.le h₁) (d₂.le h₂)
    obtain ⟨t', b₁, b₂, hxt', ht'⟩ := hG'.2 d₁.t' d₂.t' x (opOf G t) hxt (d₁.le' h₁) (d₂.le' h₂)
    refine ⟨⟨t, t', (G'.obj t').unop, ht', le_rfl⟩, ⟨(a₁.some, b₁.some, ⟨?_⟩)⟩, ⟨(a₂.some, b₂.some, ⟨?_⟩)⟩, hxt', ?_⟩
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_right))
    · exact ht'.trans (htU.trans inf_le_right)
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_left))

end CommonRef

theorem common_refinement : ∀ (X : Scheme.{0}) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ AffOp X) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K) ∧ Nonempty (H' ⋙ G' ⟶ K) ∧ IsBas (opOf K) :=
  fun X C C' _ _ _ _ G G' hG hG' =>
    ⟨CommonRef G G', inferInstance, inferInstance, CommonRef.opn G G', CommonRef.fst G G', CommonRef.snd G G',
      ⟨CommonRef.toFst G G'⟩, ⟨CommonRef.toSnd G G'⟩, CommonRef.isBas G G' hG hG'⟩

end GlobalTheory.LBObs

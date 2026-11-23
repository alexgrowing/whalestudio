import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {X Z : Scheme.{0}} (φ : Z ⟶ X) {C C' : Type} [Category.{0} C] [Category.{0} C']
  (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z)

def RefineTriple : Type :=
  {q : Pair φ × C × C' // q.1.1.2.1 ≤ opOf G q.2.1 ∧ q.1.1.1.1 ≤ opOf G' q.2.2}

instance RefineTriple.instPreorder : Preorder (RefineTriple φ G G') where
  le d e := e.1.1 ≤ d.1.1 ∧ Nonempty (d.1.2.1 ⟶ e.1.2.1) ∧ Nonempty (d.1.2.2 ⟶ e.1.2.2)
  le_refl d := ⟨le_rfl, ⟨𝟙 _⟩, ⟨𝟙 _⟩⟩
  le_trans a b c h₁ h₂ := ⟨h₂.1.trans h₁.1, ⟨h₁.2.1.some ≫ h₂.2.1.some⟩, ⟨h₁.2.2.some ≫ h₂.2.2.some⟩⟩

def RefineTriple.pair : RefineTriple φ G G' ⥤ (Pair φ)ᵒᵖ where
  obj d := Opposite.op d.1.1
  map f := (homOfLE (leOfHom f).1).op

def RefineTriple.idx [Quiver.IsThin C] : RefineTriple φ G G' ⥤ C where
  obj d := d.1.2.1
  map f := (leOfHom f).2.1.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def RefineTriple.idx' [Quiver.IsThin C'] : RefineTriple φ G G' ⥤ C' where
  obj d := d.1.2.2
  map f := (leOfHom f).2.2.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end GlobalTheory.LBObs

namespace GlobalTheory.LBObs

theorem exists_pair_refine : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  intro X Z φ C C' _ _ _ _ G G' hG hG'
  refine ⟨RefineTriple φ G G', inferInstance, inferInstance, RefineTriple.pair φ G G',
    RefineTriple.idx φ G G', RefineTriple.idx' φ G G', ⟨{ app := fun d ↦ (homOfLE d.2.1).op }⟩,
    ⟨{ app := fun d ↦ (homOfLE d.2.2).op }⟩, ?_, ?_⟩
  · intro z U hz
    obtain ⟨t, ht, -⟩ := hG.1 (φ z) ⊤ trivial
    obtain ⟨t', ht', hle⟩ := hG'.1 z (U ⊓ φ ⁻¹ᵁ opOf G t) ⟨hz, ht⟩
    refine ⟨⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle hy).2⟩, t, t'), le_rfl, le_rfl⟩,
      ht', fun y hy ↦ (hle hy).1⟩
  · intro d₁ d₂ z U hz h₁ h₂
    have k₁ : φ z ∈ d₁.1.1.1.2.1 := d₁.1.1.2 h₁
    have k₂ : φ z ∈ d₂.1.1.1.2.1 := d₂.1.1.2 h₂
    obtain ⟨t, a₁, a₂, ht, hle⟩ := hG.2 d₁.1.2.1 d₂.1.2.1 (φ z) (d₁.1.1.1.2.1 ⊓ d₂.1.1.1.2.1)
      ⟨k₁, k₂⟩ (d₁.2.1 k₁) (d₂.2.1 k₂)
    obtain ⟨t', b₁, b₂, ht', hle'⟩ := hG'.2 d₁.1.2.2 d₂.1.2.2 z
      (U ⊓ d₁.1.1.1.1.1 ⊓ d₂.1.1.1.1.1 ⊓ φ ⁻¹ᵁ opOf G t) ⟨⟨⟨hz, h₁⟩, h₂⟩, ht⟩ (d₁.2.2 h₁) (d₂.2.2 h₂)
    let d : RefineTriple φ G G' :=
      ⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle' hy).2⟩, t, t'), le_rfl, le_rfl⟩
    refine ⟨d, ⟨homOfLE ⟨?_, a₁, b₁⟩⟩, ⟨homOfLE ⟨?_, a₂, b₂⟩⟩, ht', fun y hy ↦ (hle' hy).1.1.1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.1.2, fun y hy ↦ (hle hy).1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.2, fun y hy ↦ (hle hy).2⟩

end GlobalTheory.LBObs

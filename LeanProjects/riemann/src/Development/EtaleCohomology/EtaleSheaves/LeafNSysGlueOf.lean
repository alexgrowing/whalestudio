import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodSystemGluing
open LateralTheory.E.LeafSHSysPf

theorem cocone_u_eq {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j')
    (c : Cocone D) (j j' : J) : u j ≫ c.ι.app j = u j' ≫ c.ι.app j' := by
  have h1 := c.w (IsFiltered.leftToMax j j')
  have h2 := c.w (IsFiltered.rightToMax j j')
  rw [← h1, ← h2, ← Category.assoc, ← Category.assoc, hu, hu]

theorem LeafNSysGlue_of (hR : LeafRingSys) : LeafNSysGlue := by
  intro _ B U x
  let 𝒰 := U.left.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let ι : Spec R ⟶ U.left := 𝒰.f (𝒰.idx x)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨J, _, _, D, u, hu, het, hq, c, ⟨hc⟩, hcof⟩ := hR R y
  have hE : ∀ j, Etale (Spec.map (u j) ≫ ι ≫ U.hom) := fun j => by
    have : Etale (Spec.map (u j)) := HasRingHomProperty.Spec_iff.2 (het j)
    have : Etale U.hom := U.prop
    infer_instance
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (Spec.map (u j) ≫ ι ≫ U.hom) (hE j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (u j) ≫ ι) (by show (Spec.map (u j) ≫ ι) ≫ U.hom = Spec.map (u j) ≫ ι ≫ U.hom; rw [Category.assoc]) trivial
  let tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j := fun {j j'} g =>
    MorphismProperty.Over.homMk (Spec.map (D.map g))
      (by show Spec.map (D.map g) ≫ Spec.map (u j) ≫ ι ≫ U.hom = Spec.map (u j') ≫ ι ≫ U.hom; rw [← Spec.map_comp_assoc, hu]) trivial
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  exact ⟨{
    J := J
    D := D
    V := V
    a := a
    e := fun j => Iso.refl _
    tr := tr
    tr_a := fun g => by
      apply MorphismProperty.Over.Hom.ext
      show Spec.map (D.map g) ≫ Spec.map _ ≫ ι = Spec.map _ ≫ ι
      rw [← Spec.map_comp_assoc, hu]
    tr_spec := fun g => by
      show 𝟙 _ ≫ Spec.map (D.map g) ≫ 𝟙 _ = _
      simp
    hx := fun j => by
      obtain ⟨q, hq⟩ := hq j
      refine ⟨q, ?_⟩
      rw [← hy]
      show ι (Spec.map (u j) q) = ι y
      congr 1
    c := c
    hc := hc
    cof := hcof
    t := Spec.map (c.ι.app j0) ≫ Spec.map (u j0) ≫ ι
    ht := fun j => by
      show _ = Spec.map (c.ι.app j) ≫ 𝟙 _ ≫ Spec.map (u j) ≫ ι
      rw [Category.id_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cocone_u_eq D u hu c j0 j] }⟩

end LateralTheory.E.NeighbourhoodSystemGluing

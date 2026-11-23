import Development.EtaleCohomology.EtaleSheaves.LeafLocStalkPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def SecDetect : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ X), SH A → IsUnit (q : A) → Sec.res t s = 0) → s = 0

def NbhdKillGood : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X) (x : X),
  IsUnit (q : X.residueField x) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ X), SH A → IsUnit (q : A) → Sec.res t s = 0) →
  ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0

def NbhdKillBad : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X) (x : X),
  ¬ IsUnit (q : X.residueField x) →
  ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf

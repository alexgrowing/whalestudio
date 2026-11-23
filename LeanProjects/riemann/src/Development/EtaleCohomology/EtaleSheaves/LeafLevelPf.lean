import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafLevelPf

abbrev cone0 (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) : Cx R :=
  mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g))

def LeafDisc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (g : P ⟶ Q) (n : ℤ),
  Subsingleton (HK R (mappingCone ((chains R).map (disc.map g))) F n) → Subsingleton (HK R (cone0 R g) F n)

def LeafFilt : Prop := GlobalTheory.EtC.A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E'),
  (∀ p : ℕ, ∀ n : ℤ, n < c - p → Subsingleton (HK R (cone0 R (f.app (op (SimplexCategory.mk p)))) F n)) →
  ∀ n : ℤ, n < c → Subsingleton (HK R (mappingCone ((chains R).map f)) F n)

theorem LeafLevel_of (hRel : LateralTheory.E.t_E6Cut.LeafRel) (hD : LeafDisc) (hF : LeafFilt) :
    LateralTheory.E.t_E6Cut.LeafLevel := by
  intro hA1 R _ F c E E' f h
  unfold LateralTheory.E.t_E6Cut.Conn
  rw [hRel R F c]
  apply hF hA1 R F c f
  intro p n hn
  apply hD R F _ n
  have hp := h p
  unfold LateralTheory.E.t_E6Cut.Conn at hp
  rw [hRel R F (c - p)] at hp
  exact hp n hn

end LateralTheory.E.LeafLevelPf

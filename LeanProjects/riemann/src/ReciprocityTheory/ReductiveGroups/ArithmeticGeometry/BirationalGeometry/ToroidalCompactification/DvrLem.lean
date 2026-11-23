import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section B2

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

def ExpBijF (U : UnifPre I D A G) : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen →
      (∀ t, ∃! s, U.ExpandsF F k w t s) ∧ ∀ s, ∃! t, U.ExpandsF F k w t s

end B2

def ExpBijectiveUniformisation : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G), ExpBijF U.toUnifPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Model.DvrIn (Y : Model Xo c β) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] [IsDiscreteValuationRing V] (b : O →+* V) (ϖ : V)
    (a : ArcIn D l β V b), Irreducible ϖ → IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    IsLocalHom b →
    ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ Set.range (jK V ≫ y') ⊆ Set.range Y.j ∧
      Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ y'

def DvrInSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → Y.DvrIn

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

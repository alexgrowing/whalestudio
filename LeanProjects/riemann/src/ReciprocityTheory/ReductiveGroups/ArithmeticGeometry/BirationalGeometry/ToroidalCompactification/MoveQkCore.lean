import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

def cU {F : Type} [Field F] (u : F) (hu : u ≠ 0) : Γ(Sp F, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 u hu)

theorem gm_cU {F : Type} [Field F] (u : F) (hu : u ≠ 0) (z : Sp F) : (gm (𝟙 (Sp F)) z ⊤ (cU u hu)).val = toStk z u := by
  simp [gm, cU, toStk, pullU]
  rfl

section Move

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
  {Φ : D'.P.A.left ⟶ D.P.A.left}

def OmW (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (F : Type) [Field F] [Algebra (FractionRing R') F] (y : Sp F)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) (x : TF (R := R') F ⟶ D'.P.A) :
    ((Sp F).presheaf.stalk y)ˣ := gw w x.left y (J (x.left ≫ Φ)) (J' x.left)

end Move

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

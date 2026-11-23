import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

def splitTorus_isCommMonObjSt : Prop :=
  ∀ (S : Scheme.{u}) (X : Type u) [AddCommGroup X], IsCommMonObj (splitTorus S X)

def characters_splitTorusSt : Prop :=
  ∀ (S : Scheme.{u}) [Nonempty S] [ConnectedSpace S] (X : Type u) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X],
    ∃ e : X ≃ characters (splitTorus S X),
      ∀ a b : X, (e (a + b)).1 = lift (e a).1 (e b).1 ≫ μ

def mulN_isMonHomSt : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (mulN G m)

end ReciprocityTheory.ChartRestriction.G.Semi

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidityTranslation

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def rigidifiedBundle {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (hrig : rig.IsGen) : RigLB P.A :=
  ⟨P.L, rig, P.isLB, hrig⟩

def Cube : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen),
    Nonempty (CubicalStr P.A (rigidifiedBundle P rig hrig)) ∧
      Subsingleton (CubicalStr P.A (rigidifiedBundle P rig hrig))

def translate {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ A :=
  lift (fst T A ≫ x) (snd T A) ≫ μ[A]

def squareBundle {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (x y : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 4)
    ![(translate A (lift x y ≫ μ[A])).left, (snd T A).left, (translate A x).left,
      (translate A y).left]
    ![1, 1, -1, -1]

def Square : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (T : Over S) (x y : T ⟶ P.A),
    ∃ N : LB T.left, N.IsLB ∧
      ∃ u : LB.Iso (N.pull (fst T P.A).left) (squareBundle P.A P.L x y), u.IsGen

def Rigidity : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B →
      ∀ f : A ⟶ B, η[A] ≫ f = η[B] → IsMonHom f

def GlobalFunctions : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → Function.Bijective (A.hom.appTop).hom

def Laws : Prop := Cube ∧ Square ∧ Rigidity ∧ GlobalFunctions

example {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translate A (toUnit T ≫ η[A]) = snd T A := by
  have h : fst T A ≫ toUnit T = toUnit (T ⊗ A) := toUnit_unique _ _
  unfold translate
  rw [← Category.assoc, h, MonObj.lift_comp_one_left]

example {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    translDiff A L x =
      LB.LinComb L (K := Fin 2) ![(translate A x).left, (snd T A).left] ![1, -1] := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.RigidityTranslation

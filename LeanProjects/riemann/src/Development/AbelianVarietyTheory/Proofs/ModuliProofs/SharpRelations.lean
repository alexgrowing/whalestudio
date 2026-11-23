import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

noncomputable section
namespace GlobalTheory.SharpRel

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by
  have hl : x.left ≫ φ = y.left ≫ φ := congrArg CommaMorphism.left e
  ext1
  exact h.1.hom_ext hl (by rw [Over.w x, Over.w y])

theorem push_comp (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]

end

def postHom {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] (p : A ⟶ C) [IsMonHom p] (T : Over S) :
    (T ⟶ A) →* (T ⟶ C) :=
  MonoidHom.mk' (· ≫ p) fun x y => MonObj.mul_comp x y p

end GlobalTheory.SharpRel
end

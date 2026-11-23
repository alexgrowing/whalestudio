import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def QuotientByFiniteFlatStatement : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
    ∀ (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h →
    ∃ (A' : Over (Spec (CommRingCat.of R))) (_ : GrpObj A') (L' : LB A'.left) (q : A ⟶ A'),
      IsAbelianScheme A' ∧ L'.IsLB ∧ Out.RelAmple A' L' ∧ IsMonHom q ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
        z ≫ q = 1 ↔ ∃ φ : B →ₐ[R] S, spMap φ ≫ h = z

end GlobalTheory.CompanionTheory.Ar.GR

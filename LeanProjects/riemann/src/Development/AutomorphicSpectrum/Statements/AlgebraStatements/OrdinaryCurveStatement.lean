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

def SubquotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ (N : Type) [AddCommGroup N] (M : Submodule R (N → C)), IsAbFactor p M →
    ∀ K : AddSubgroup N, GenAF p M K

def OrdinaryCurveStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∃ (A : Over (Spec (CommRingCat.of R))) (_ : GrpObj A) (L : LB A.left), IsAbelianScheme A ∧ L.IsLB ∧
    Out.RelAmple A L ∧ ∃ (T : TorsRep A p) (pt : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ A)),
      IsTorsPts A p pt ∧ torsFun C T pt =
        tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
          (intFun R (ZMod p))

end GlobalTheory.CompanionTheory.Ar.GR

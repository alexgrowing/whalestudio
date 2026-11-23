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

def HodgeTateDatumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ [Algebra ℤ_[p] R] (P : Out.PolAV (Spec (CommRingCat.of R))),
    Nonempty (TorsRep P.A p) ∧
    ∃ (cp : R) (_ : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
      (H : HodgeTateDatum p P.g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p P.g → (sp (R₀ := R) R ⟶ P.A)),
      IsTorsPts P.A p pt ∧ ∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt

end GlobalTheory.CompanionTheory.Ar.GR

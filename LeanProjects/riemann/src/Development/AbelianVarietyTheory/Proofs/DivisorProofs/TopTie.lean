import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def TopTie (G : GridData Lc sc) (i j : Fin D.R.m) {WW : HSp D}
    (X : Tri T (G.V (.grid (i + 1) (j + 1))) (G.V (.grid i j)) WW) : Prop :=
  (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank = WW.rank ∧
    (∃ (ι₁ : (G.V (.grid i (j + 1))).V →ₗ[D.host.E] WW.V) (ι₂ : (G.V (.grid (i + 1) j)).V →ₗ[D.host.E] WW.V),
      Formalism.BasicNotions.HSpace.IsIsomEmb (G.V (.grid i (j + 1))) WW ι₁ ∧ Formalism.BasicNotions.HSpace.IsIsomEmb (G.V (.grid (i + 1) j)) WW ι₂ ∧
      (∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) ∧
      ∀ z : WW.V, WW.frame.equivFun z ∈ X.rW.Λ ↔ ∃ x y, (G.V (.grid i (j + 1))).frame.equivFun x ∈ G.Λ (.grid i (j + 1)) ∧
        (G.V (.grid (i + 1) j)).frame.equivFun y ∈ G.Λ (.grid (i + 1) j) ∧ z = ι₁ x + ι₂ y) ∧
    X.rA.Λ = G.Λ (.grid (i + 1) (j + 1)) ∧ X.rA'.Λ = G.Λ (.grid i j)

end GlobalTheory.SqTower

end

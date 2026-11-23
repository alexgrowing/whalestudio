import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base PsiUnr stepFac)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

open Classical in

def chs (G : GridData Lc sc) (i j : Fin D.R.m) (t : T) : Chars D.host.F D.host.E where
  α := Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)
  β := G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)
  S₀ := G.pl.S0
  Q := (twPl G t).image fun w => w.under (𝓞 D.host.F)

def BaseFits (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t : T) (B : Base D.host.F D.host.E) : Prop :=
  B.ψ = W.ψ ∧ (chs G i j t).T ⊆ B.P ∧ (∀ v ∈ B.P, PsiUnr B.ψ v) ∧
    ∀ v : B.P, v.1 ∈ (chs G i j t).T → GlobalTheory.AdelicU.splitPrime (B.τ v) ∈ locPl G t

end GlobalTheory.SqStep

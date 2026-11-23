import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FirstRowEndLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

open Classical in

def stepType (L : LevCh D T) (t : T) (w : Pl D.host.E) (j : ℕ) : TypeDatum (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) :=
  if w ∈ L.Pg then
    (TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j
  else if h : w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹ then parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ h.2
  else TypeDatum.full _ _

open Classical in

def endLamAt (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ) (κ : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)) : ℂ :=
  if h : (reGL (ixFin G t w j)).symm κ ∈ (stepType L t w j).J then (((stepType L t w j).lam ⟨_, h⟩)⁻¹ : ℂˣ) else 1

def endLam (G : GridData L sc) (t : T) (w : Pl D.host.E) (κ : GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w)) : ℂ :=
  endLamAt G t w D.R.m κ

end GlobalTheory.FirstRowEndLaw

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidifications
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_rank_bound : GlobalTheory.FunPr.Hypotheses₂ → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  first | exact @GlobalTheory.SqTower.StageExists.stage_exists | exact GlobalTheory.SqTower.StageExists.stage_exists | (intros; apply GlobalTheory.SqTower.StageExists.stage_exists <;> assumption)

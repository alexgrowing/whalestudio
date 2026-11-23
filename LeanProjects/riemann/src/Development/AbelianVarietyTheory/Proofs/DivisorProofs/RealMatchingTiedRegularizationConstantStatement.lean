import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMatchingTiedRegularizationConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_matching_tied_regularization_constant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W, ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧
    ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, RegConst W B ρ₀ t i j c₀ := by
  first | exact @GlobalTheory.GridFrameExistence.exists_tied | exact GlobalTheory.GridFrameExistence.exists_tied | (intros; apply GlobalTheory.GridFrameExistence.exists_tied <;> assumption)

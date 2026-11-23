import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareConstantProportionalRegular
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_constant_proportional_regular : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
    ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' → RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  first | exact @GlobalTheory.RealSep.real_matching | exact GlobalTheory.RealSep.real_matching | (intros; apply GlobalTheory.RealSep.real_matching <;> assumption)

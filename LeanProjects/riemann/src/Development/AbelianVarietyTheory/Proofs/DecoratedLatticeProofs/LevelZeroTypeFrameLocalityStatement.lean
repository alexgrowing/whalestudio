import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroTypeFrameLocality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_zero_type_frame_locality : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (hc : 0 + (G.s + 1) = G.s + 1) (x : G.S.P.J) (y : GA D (d.st 0).V), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) hc) y ((GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))) → Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0) ∈ Formalism.L2.DIV.St (d.st 0).β → G.Red x (Formalism.L2.DIV.upperLeftBlock hr (Formalism.L2.DIV.redFn (d.st 0).β PP (Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)))) := by
  first | exact @GlobalTheory.ReadAtBase.red_of_isLoc | exact GlobalTheory.ReadAtBase.red_of_isLoc | (intros; apply GlobalTheory.ReadAtBase.red_of_isLoc <;> assumption)

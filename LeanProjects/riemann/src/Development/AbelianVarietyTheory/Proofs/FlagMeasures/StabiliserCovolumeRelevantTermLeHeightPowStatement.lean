import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  first | exact @GlobalTheory.LoopVol.volRC_le | exact GlobalTheory.LoopVol.volRC_le | (intros; apply GlobalTheory.LoopVol.volRC_le <;> assumption)

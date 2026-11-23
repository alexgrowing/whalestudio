import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_step_weil_datum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.stageY W j).V (GlobalTheory.BaseChain.stageY W (j + 1)).V ((GlobalTheory.BaseChain.com W).chS (j + 1)) ((GlobalTheory.BaseChain.com W).chT (j + 1)) (GlobalTheory.BaseChain.stepY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.com W).θ (GlobalTheory.BaseChain.stageY W j).V (GlobalTheory.BaseChain.stageY W (j + 1)).V (cart (GlobalTheory.BaseChain.stageY W j).M) (cart (GlobalTheory.BaseChain.stageY W (j + 1)).M) (GlobalTheory.BaseChain.stageY W j).Λ (GlobalTheory.BaseChain.stageY W (j + 1)).Λ (GlobalTheory.BaseChain.stageY W j).β (GlobalTheory.BaseChain.stageY W (j + 1)).β (GlobalTheory.BaseChain.stageY W j).L ((GlobalTheory.BaseChain.com W).chi (j + 1)) ∅ ξ f₀ (GlobalTheory.BaseChain.stepY f j).f := by
  first | exact @GlobalTheory.BaseChain.stepY_weil_vec | exact GlobalTheory.BaseChain.stepY_weil_vec | (intros; apply GlobalTheory.BaseChain.stepY_weil_vec <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageYValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageXValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepWeilDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopWeilDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

open GlobalTheory.ChainOnto

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem stepY_is {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (hP : PkHyp W) (hf : f.RowOK) (j : ℕ) (hj : j + 1 < D.R.m) :
    (stepY f j).Is (j + 1) :=
  ⟨(GlobalTheory.T.base_chain_step_weil_datum W u f hP hf j hj).1, (GlobalTheory.T.base_chain_step_weil_datum W u f hP hf j hj).2, (GlobalTheory.T.base_chain_step_theta_functions W u f hP hf j hj).1,
    (GlobalTheory.T.base_chain_step_theta_functions W u f hP hf j hj).2, GlobalTheory.T.base_chain_step_theta_lift W u f hP hf j hj⟩

theorem stepX_is {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (hP : PkHyp W) (hf : f.RowOK) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) : (stepX f j h).Is (j + 1 + 1) :=
  ⟨(GlobalTheory.T.base_chain_top_weil_datum W u f hP hf j h).1, (GlobalTheory.T.base_chain_top_weil_datum W u f hP hf j h).2, (GlobalTheory.T.base_chain_top_theta_functions W u f hP hf j h).1,
    (GlobalTheory.T.base_chain_top_theta_functions W u f hP hf j h).2, GlobalTheory.T.base_chain_top_theta_lift W u f hP hf j h⟩

theorem reach_dn {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (hP : PkHyp W) (hf : f.RowOK) :
    ∀ k, k + 1 ≤ D.R.m → Reach (com W) (stageY W 0) k (stageY W k) ((f.t W.P.A3.A.μ0).dn k)
  | 0, _ => Reach.zero
  | k + 1, hk => Reach.step (reach_dn f hP hf k (by omega)) (GlobalTheory.T.base_chain_stage_Y_valid W hP (k + 1) (by omega)) (stepY f k)
      (stepY_is f hP hf k (by omega))

theorem linkOnto_of_ontoAll : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word),
    PkHyp W → GlobalTheory.ChainOnto.OntoAll D → ∀ f : FamCh W u, f.RowOK → LinkOnto f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP hO f hf n h T hT
  have e : 2 * n + 1 + 1 = D.R.m := by omega
  have hX : (stageX W).Is (com W) (2 * n + 1 + 1) := e ▸ GlobalTheory.T.base_chain_stage_X_valid W hP
  have hR := Reach.step (reach_dn f hP hf (2 * n + 1) (by omega)) hX (stepX f (2 * n) h) (stepX_is f hP hf (2 * n) h)
  obtain ⟨G, hG⟩ := hO hP.gap (com W) (GlobalTheory.T.base_chain_commutation_valid W hP) (stageY W 0) (GlobalTheory.T.base_chain_stage_Y_valid W hP 0 (by omega)) (2 * n + 1 + 1) (by omega)
    _ _ hR ⟨T, GlobalTheory.T.rows_mem_base_chain_stage_zero W hP T hT⟩
  exact ⟨G, congrArg Subtype.val hG⟩

end GlobalTheory.BaseChain

end

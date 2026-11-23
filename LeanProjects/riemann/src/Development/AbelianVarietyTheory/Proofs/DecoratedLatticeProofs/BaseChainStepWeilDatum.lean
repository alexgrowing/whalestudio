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

namespace GlobalTheory.BaseChain

theorem stepY_weil_vec : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.stageY W j).V (GlobalTheory.BaseChain.stageY W (j + 1)).V ((GlobalTheory.BaseChain.com W).chS (j + 1)) ((GlobalTheory.BaseChain.com W).chT (j + 1)) (GlobalTheory.BaseChain.stepY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.com W).θ (GlobalTheory.BaseChain.stageY W j).V (GlobalTheory.BaseChain.stageY W (j + 1)).V (cart (GlobalTheory.BaseChain.stageY W j).M) (cart (GlobalTheory.BaseChain.stageY W (j + 1)).M) (GlobalTheory.BaseChain.stageY W j).Λ (GlobalTheory.BaseChain.stageY W (j + 1)).Λ (GlobalTheory.BaseChain.stageY W j).β (GlobalTheory.BaseChain.stageY W (j + 1)).β (GlobalTheory.BaseChain.stageY W j).L ((GlobalTheory.BaseChain.com W).chi (j + 1)) ∅ ξ f₀ (GlobalTheory.BaseChain.stepY f j).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hC := hW.bot.hyp.2.2.2.1
  have hQ : (pk W).Q W.P.A3.A.μ0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun PP => GlobalTheory.MiTop.not_mem_Q_base W PP
  refine ⟨hC.chain.ωY W.P.A3.A.μ0 j hj, (pk W).xiR W.P.A3.A.μ0, (pk W).vac j, ?_⟩
  have h := (hf.row W.P.A3.A.μ0).vP j hj
  rw [hQ] at h
  exact h

end GlobalTheory.BaseChain

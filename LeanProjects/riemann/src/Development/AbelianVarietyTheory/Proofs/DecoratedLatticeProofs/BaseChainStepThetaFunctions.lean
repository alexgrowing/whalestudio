import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

variable {D : D7}

theorem rank_Yc_le_succ (j : ℕ) : (Yc D j).rank ≤ (Yc D (j + 1)).rank := by
  rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.Y_rank _ (min_le_right _ _)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_min_right D.R.m (Nat.le_succ j))) _

theorem stepY_thetaFun_isItW : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j, j + 1 < D.R.m → (∀ φ, IsThetaFunO (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.stageY W j).V (GlobalTheory.BaseChain.stageY W (j + 1)).V ((GlobalTheory.BaseChain.stepY f j).pt φ)) ∧ IsItW (GlobalTheory.BaseChain.com W).θ (GlobalTheory.BaseChain.stageY W j).M (GlobalTheory.BaseChain.stageY W (j + 1)).M (GlobalTheory.BaseChain.stepY f j).ω (GlobalTheory.BaseChain.stepY f j).pt (GlobalTheory.BaseChain.stepY f j).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j hj
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have hj' : j < D.R.m := by omega
  have dS : IsSelfDualC (Yc D j) ((pk W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY j hj')
  have dT : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY (j + 1) hj)
  have hP' := (hR.row W.P.A3.A.μ0).vP j hj
  have hY := hC.chain.vY W.P.A3.A.μ0 j hj
  have hω := hC.chain.ωY W.P.A3.A.μ0 j hj
  have hθ := hC.models.inf
  obtain ⟨vth, vne, -⟩ := GlobalTheory.InnerSteps.stepVec_vac dS dT (rank_Yc_le_succ j) hP'
  refine ⟨fun φ => GlobalTheory.FockTheta.ptStable D _ _ hP'.1.1 hθ _ _ _ _ _ _ _ φ vth, ?_⟩
  have h0 := GlobalTheory.Grid.isItW_of_mem_span hω hθ hP'.1.2.theta (GlobalTheory.Grid.stepVec_mem_span dS dT hY)
    (hC.chain.ItY W.P.A3.A.μ0 j hj)
  exact GlobalTheory.Grid.isItW_of_mem_span hω hθ vth (GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hP'.1 dS dT (GlobalTheory.Grid.stepVec_mem_span dS dT hP') vne) h0

end GlobalTheory.BaseChain

end

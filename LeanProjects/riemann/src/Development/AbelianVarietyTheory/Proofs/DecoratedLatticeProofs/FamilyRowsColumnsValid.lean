import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanConsecutiveSpacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanLastStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalarStatement
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

namespace GlobalTheory.Fam.IsFam

theorem main : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hP f hR
  have hC := hP.bot.hyp.2.2.2.1
  have hstd : IsStdChar D (pk W).ψ (-1) := (hC.chain.ωX W.P.A3.A.μ0).std
  have hinf : IsInfFam (pk W).θ := hC.models.inf
  have spanT : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n)) (pk W).ItX e) := by
    intro n e
    subst e
    exact GlobalTheory.T.iterates_span_last_step hDS hHC W hP
  refine ⟨⟨hstd, hinf, hR.x, (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D D.sp.X').2 GlobalTheory.Hk3.StepX.gram_posDef_X,
    hR.meas.μf, hR.meas.ρJ, hR.meas.ρB, fun j hj => GlobalTheory.T.iterates_span_consecutive_spaces hDS hHC W hP j hj, fun j h => spanT _ (idx_top h)⟩, fun hCol t => ?_⟩
  exact
    { sBF := fun j ρ h => ⟨((hR.row t).sBF j ρ h).1, ((hR.row t).sBF j ρ h).2.1⟩
      sFB := fun j σ h => ⟨((hR.row t).sFB j σ h).1, ((hR.row t).sFB j σ h).2.1⟩
      pt := fun j hj P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vP j hj)) P
      ptT := fun j h P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vT j h)) P
      CC := fun j _ => ⟨_, _, le_rfl⟩
      CT := ⟨_, _, le_rfl⟩
      io := GlobalTheory.T.theta_lift_chain_scalar W u hP f hR t
      ioT := GlobalTheory.T.theta_lift_top_scalar W u hP f hR t
      cI := fun j hj => hR.meas.cIOf_ne_zero (lvP W) t j hj
      ker := hCol.ker t
      e := hCol.e t
      eT := hCol.eT t
      stabK := hCol.stabK t
      stabS := hCol.stabS t }

end GlobalTheory.Fam.IsFam

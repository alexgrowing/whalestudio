import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_components_share_cmData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  first | exact @GlobalTheory.ShareOn.comps_share | exact GlobalTheory.ShareOn.comps_share | (intros; apply GlobalTheory.ShareOn.comps_share <;> assumption)

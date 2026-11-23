import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mul_and_faithful_finiteGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m), (∀ g g' : p.P.Gp, r.lev i (g * g') = r.lev i g * r.lev i g') ∧ ∀ g : p.P.Gp, r.lev i g = 1 → g = 1 := by
  first | exact @GlobalTheory.LevelFaithful.lev_mul_and_faithful | exact GlobalTheory.LevelFaithful.lev_mul_and_faithful | (intros; apply GlobalTheory.LevelFaithful.lev_mul_and_faithful <;> assumption)

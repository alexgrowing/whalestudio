import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGram
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_norm_has_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, HasGram (nrmR p.R.toRealDat i) := by
  first | exact @GlobalTheory.CovTop.GramPt.hasGram_at | exact GlobalTheory.CovTop.GramPt.hasGram_at | (intros; apply GlobalTheory.CovTop.GramPt.hasGram_at <;> assumption)

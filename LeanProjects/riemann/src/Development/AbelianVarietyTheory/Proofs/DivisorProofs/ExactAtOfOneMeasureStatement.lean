import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_at_of_one_measure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D → ∀ i : Fin D.R.m, ExactAt p i := by
  first | exact @GlobalTheory.CovTop.MeasRd.exactAt_of_rows | exact GlobalTheory.CovTop.MeasRd.exactAt_of_rows | (intros; apply GlobalTheory.CovTop.MeasRd.exactAt_of_rows <;> assumption)

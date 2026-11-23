import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eV0_eq_iC_Pq_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  first | exact @GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq | exact GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq | (intros; apply GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq <;> assumption)

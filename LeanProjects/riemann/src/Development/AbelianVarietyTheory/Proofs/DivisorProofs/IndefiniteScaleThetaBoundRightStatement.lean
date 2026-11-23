import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundRight
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_bound_right : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → RowsB B := by
  first | exact @GlobalTheory.RowsAtRealTBClose.rowsB_of_decay | exact GlobalTheory.RowsAtRealTBClose.rowsB_of_decay | (intros; apply GlobalTheory.RowsAtRealTBClose.rowsB_of_decay <;> assumption)

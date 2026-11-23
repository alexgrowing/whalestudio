import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSum
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_sum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), RealPins Q → Q.FramesEx := by
  first | exact @GlobalTheory.FramesAtReal.framesEx_of_realisation | exact GlobalTheory.FramesAtReal.framesEx_of_realisation | (intros; apply GlobalTheory.FramesAtReal.framesEx_of_realisation <;> assumption)

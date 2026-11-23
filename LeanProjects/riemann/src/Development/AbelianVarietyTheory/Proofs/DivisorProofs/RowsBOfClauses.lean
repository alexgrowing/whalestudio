import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisationStatement
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj Formalism.L2 Formalism.L2.Rows Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsAtRealTB

set_option maxHeartbeats 1000000 in
theorem rowsB_of_clauses : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → B.Q.Rl.toRealDat.LUnif → IoExt B.Q.Rl.toRealDat → RowsB B := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
  exact ⟨hIo, fun i => GlobalTheory.T.oneMapRowR_of_weakCharacterisation D _ _ _ _ P.A3 B.T B.Q.Rl (faceT P Dcf Spf Zscf) B.κ B.v₀ B.O (phEff B.Q.Rl)
    hn B.Q.charW hEx ⟨B.fw⟩ hIo i (B.pins i) (B.phase i hUnif)⟩

end GlobalTheory.RowsAtRealTB

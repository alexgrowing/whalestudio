import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

structure STiesR (R : Formalism.L2.RecT ex) extends STies D where

  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u ((R.T.cols.forms u).to0)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK

  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x

  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D

  G : Formalism.L2.SG.RowDict.GoodOp X
  rowTie : ∀ hF : FinX Y, Formalism.L2.SG.RowDict.RowDictTie X G (hI hF).eHH

  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

theorem STiesR.concTie {R : Formalism.L2.RecT ex} (T : STiesR R) (hF : FinX T.Y) (hK : T.X.LevelSubgroupNormalized)
    (hN : ∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu T.X u T.Y.hK) (hW : Formalism.L2.SG.WuDecay.WuDecay T.X)
    (hph : Integrable T.X.ph (Formalism.L2.SG.ProjRows.muInf T.X.B.I)) (hTF : Formalism.L2.SG.RowsConc.TFrameAt D) :
    Formalism.L2.SG.RowsConc.ConcTie T.X T.Y :=
  T.toSTies.concTie hF hK hN hW hph T.locTied hTF

end Formalism.L2.SG.SpectralTiesReal

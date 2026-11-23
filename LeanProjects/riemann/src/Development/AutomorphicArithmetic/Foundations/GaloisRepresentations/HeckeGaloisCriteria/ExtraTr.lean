import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.BuDefQEta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.KapSharpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.NchTieTr

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (c : CutD D)

def raw : Gen.Raw D :=
  ⟨(layCut D c).eta, (layCut D c).eta_nonneg, (layCut D c).reEta _ (layCut D c).eta_nonneg, (layerCut_admissible D c).reEta _ _,
    (layCut D c).etaOk_reEta⟩

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (cut D c) := Gen.ledTr (raw c) L

theorem tiesTr (h : Ties D) : Ties (raw c).rec' := Gen.tiesTr (raw c) h h.tw_cover

set_option maxHeartbeats 1600000 in

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (raw c).rec' (Gen.ledTr (raw c) L) (Gen.gatTr (raw c) gatT) (Gen.instTr (raw c) Gx) (Gen.latTr (raw c) Gy) K
      (Gen.divTr (raw c) X) cX :=
  Gen.extraTr (raw c) ex (nchTr c ex.nch) (nchTie_tr c ex.nch_tie) (xdTr c ex.xd)
    (show BaseLevelRowSide (cut D c) from ⟨sideTr c ex.p0.s⟩) (rrDef_tr c _ ex.rationalRoots_def) (ambTr c ex.amb) (ambTr c ex.amb0) (kapSharp_tr c)

end UpperTheory.GalC

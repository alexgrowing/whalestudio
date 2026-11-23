import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

set_option linter.dupNamespace false

namespace Formalism.L2.SG.SettingExistsMeasured

variable {D : D7}

def withMeas (X : HidaSetting D) (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS)
    (hg : mg.IsTextNorm)
    (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
      (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
        crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
    (hw : ∀ u, (mw u).IsTextNorm) : HidaSetting D :=
  { X with measG := mg, measG_norm := hg, measW := mw, measW_norm := hw }

variable (D)

def RescaleStep : Prop :=
  ∀ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I), X.MeasTie hb →
    ∃ (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS) (hg : mg.IsTextNorm)
      (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
        (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
          crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
      (hw : ∀ u, (mw u).IsTextNorm),
      (withMeas X mg hg mw hw).MeasTie hb ∧
      ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ (withMeas X mg hg mw hw) ψ ∧
        ∀ w, Formalism.L2.SG.LocVol.LocCompatX (withMeas X mg hg mw hw) ψ w

def SettingExistsMeasured (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    X.MeasTie hb ∧
    (∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
      Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
    Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Formalism.L2.SG.ColDict.Transport X u (F u), Formalism.L2.SG.ColDict.LevelMatch X Tr hK

def trMeas {X : HidaSetting D} {mg hg mw hw} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (Tr : Formalism.L2.SG.ColDict.Transport X u F) : Formalism.L2.SG.ColDict.Transport (withMeas X mg hg mw hw) u F where
  wt := Tr.wt
  wt_isom := Tr.wt_isom
  wt_e := Tr.wt_e
  wt_f := Tr.wt_f
  weight_z := Tr.weight_z
  ιA := Tr.ιA
  ιA_rat := Tr.ιA_rat
  ιA_int := Tr.ιA_int
  h0 := Tr.h0
  hc := Tr.hc
  hc_rep := Tr.hc_rep
  J := Tr.J
  J_eqv := Tr.J_eqv
  J_val := Tr.J_val
  J_isom := Tr.J_isom

end Formalism.L2.SG.SettingExistsMeasured

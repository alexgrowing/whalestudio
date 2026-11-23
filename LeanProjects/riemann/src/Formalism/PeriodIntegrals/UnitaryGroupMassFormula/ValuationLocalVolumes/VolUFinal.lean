import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolUHerm : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, TypAt X v → VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS

theorem volTypV_of_herm (hH : VolUHerm X ψ) : VolTypV X u u' ψ :=
  volTypV_of_cnt X u u' ψ Formalism.L2.SG.Pf.conductor_inverse_different (fun hh => hH hh.1 hh.2.1)
    (fun _ v hv => volTTFCong_of X u u' v hv)

def VolUHermBox : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, TypAt X v →
    VolUHm.VolTHermBox X.B.I.cm.sig v D.R.rS ψ (gAt X v)

theorem volUHerm_of_box (hB : VolUHermBox X ψ) : VolUHerm X ψ := by
  intro hψ hs v hv
  obtain ⟨-, -, hd⟩ := VolUT.typ_arith X v hv
  have hinv : ∀ y : X.B.I.E, X.B.I.cm.sig (X.B.I.cm.sig y) = y := fun y => star_star y
  exact VolUHm.volTHermCnt_of_box X.B.I.cm.sig v D.R.rS ψ hψ X.B.I.cm.deg2
    (VolUTr.annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) hd hinv (gAt X v) (hB hψ hs v hv)

theorem volTypV_of_box (hB : VolUHermBox X ψ) : VolTypV X u u' ψ :=
  volTypV_of_herm X u u' ψ (volUHerm_of_box X ψ hB)

end Formalism.L2.SG.Pf.NcVal

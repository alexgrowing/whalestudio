import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def retie (D : D7) : D7 :=
  letI := D.host.cmStar
  { D with
    vol := fun W => Vol.trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    vol_pos := fun W => Vol.trueVol_pos D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    dsig := fun τ => Per.posOr1 (Vol.trueDsig D.R (D.hc τ))
    dsig_pos := fun _ => Per.posOr1_pos _
    s := { D.s with cdScale := Vol.trueScale D.cd, cdScale_pos := Vol.trueScale_pos D.cd }
    gx := Per.trueGx D.host D.what₂.embLL D.embE D.eTau }

end GlobalTheory.Mem

import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

def FullTiedNoG.cols {D : D7} (X : FullTiedNoG D) : ColsHerm D where
  base := X.base.toHermCols
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

set_option maxHeartbeats 4000000 in

def colsHermSet (C : ColsHerm D) : ColsHerm (setGat D g' hd') where
  base := colsSet D g' hd' C.base
  atT := fun u => atTSet D g' hd' (C.atT u)
  levelZeroCompatibility := C.levelZeroCompatibility
  ad := adSet D g' hd' _ _ C.ad
  cof := C.cof
  piG := C.piG
  stabMap := C.stabMap
  fvI := C.fvI
  std := C.std
  baseL := C.baseL

set_option maxHeartbeats 8000000 in
theorem jointSet' (C : ColsHerm D) {u : D.what₂.Word} (T : FormsTied D u) (h : Joint C u T) :
    Joint (colsHermSet D g' hd' C) u (formsSet D g' hd' T) := { h with }

set_option maxHeartbeats 8000000 in

def columnsWithReplacedGroup (C : ColsTied D) : ColsTied (setGat D g' hd') where
  herm := colsHermSet D g' hd' C.herm
  forms := fun u => formsSet D g' hd' (C.forms u)
  joint := fun u => jointSet' D g' hd' C.herm (C.forms u) (C.joint u)
  gl_const := C.gl_const
  chi := C.chi
  fr_const := C.fr_const
  frP_const := C.frP_const

end Formalism.L2.G

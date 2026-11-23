import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrJ
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms Formalism.UG Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.factResChar

section Joints

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Joints

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))

section RecG

variable (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def noG_recG (H : FullTiedNoG D) : FullTiedNoG (recG D sc Ce Lc X hd) := fullSet D _ hd H

def hermitianFormsOfRecursiveGroup (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) : FullTied (recG D sc Ce Lc X hd) :=
  (noG_recG D sc Ce Lc X hd H).toFull fun u w hg => levTieOf (hL u) (levTieG D sc Ce Lc X hd u w hg)

def formsOfRecursiveGroup {u : D.what₂.Word} (T : Forms0 D u) : Forms0 (recG D sc Ce Lc X hd) u := forms0Set D _ hd T

end RecG

end Formalism.L2.G

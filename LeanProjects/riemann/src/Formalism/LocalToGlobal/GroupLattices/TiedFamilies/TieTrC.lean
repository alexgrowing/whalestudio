import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.RecursiveTieLevelZeroEq
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms Formalism.UG Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev levelZeroHermitianTransport (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) : Herm0 (recC D sc Ce Lc I ψ hd) :=
  (hermitianFormsOfRecursiveGroup D sc Ce Lc (packC D Lc I ψ) hd H hL).to0

abbrev formsOfRecursion (T : ∀ u : D.what₂.Word, Forms0 D u) : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u :=
  fun u => formsOfRecursiveGroup D sc Ce Lc (packC D Lc I ψ) hd (T u)

set_option maxHeartbeats 4000000 in

def secondLayerCompatibilities (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (CH : Cmp.CmpHyp (formsOfRecursion D sc Ce Lc I ψ hd T) (gatTiesC D sc Ce Lc I ψ hd)
      (cmpInC D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL B hBs hB)) :
    GroupCompatibilityAll (recC D sc Ce Lc I ψ hd) (gatTiesC D sc Ce Lc I ψ hd)
      (Cmp.latCmpC (formsOfRecursion D sc Ce Lc I ψ hd T) (gatTiesC D sc Ce Lc I ψ hd)
        (cmpInC D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL B hBs hB) CH) :=
  groupCompatibilityOfRecursion D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL (formsOfRecursion D sc Ce Lc I ψ hd T) B hBs hB CH
    fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)

end Formalism.L2.G

import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieAll
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrC
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsiC

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp Formalism.L2.Herm

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (H : FullTiedNoG D)
  (I0 : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)

def idStd : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  fun u w hg => locIdStd D u w hg (I0 u w hg) B hBs
    (Classical.choose (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))
    (Classical.choose_spec (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))

theorem idStd_fr (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) :
    (idStd D H I0 B hBs u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((idStd D H I0 B hBs u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B := rfl

variable (sc : Scale) (Ce : ℝ) (T : ∀ u : D.what₂.Word, Forms0 D u)
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (H.base.lev0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

structure LeftD : Prop where

  joint : ∀ u, Joint0 H.base.lev0 u (T u)

  blk : ∀ u w hg, BlockRationalityAtPlace (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (gatTiesC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) u w hg B

  psi0 : ∀ u, LevelZeroCharacterRational (D := recC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) (formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) u

  psi : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
      (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
      (((formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) u).cls0).lev (H.base.lev0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
      ((cmpInC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (fun _ => rfl) B hBs (idStd_fr D H I0 B hBs)).embW u w hg) (ψ u w hg)

  valInt : ValIntRec (formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) (gatTiesC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) (cmpInC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (fun _ => rfl) B hBs (idStd_fr D H I0 B hBs))

variable {D H I0 B hBs sc Ce T ψ hd}

end Formalism.L2.G

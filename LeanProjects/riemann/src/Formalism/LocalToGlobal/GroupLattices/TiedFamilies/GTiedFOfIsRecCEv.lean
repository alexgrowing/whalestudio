import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

inductive IsRecC (D : D7) (Gt : GatTies D) (c : LatCmp D) : Prop
  | intro
    (D0 : D7)
    (sc : Scale)
    (Lc : ∀ u, ColLevel D0.R D0.host.F D0.host.E D0.sp D0.host.g (D0.mem u).C (D0.mem u).A (D0.clsLat u))
    (I : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      LocId (Lc u) (D0.what₂.places.resChar w) (nOrb (zH D0.R.toFrame (hP D0 (D0.what₂.places.resChar w))))
      (WQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w)))
      (QQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w))))
    (ψ : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D0.what₂.places.resChar w) →* (ORec D0 w (nFr D0 (D0.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D0 Lc I ψ u w h).gat (rSc sc D0.R.k (D0.what₂.places.resChar w))
      (epSc D0.R sc 1 (D0.what₂.places.resChar w))).d = Module.finrank ℂ (D0.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D0 sc 1 Lc I ψ hd))
    (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D0.what₂.Word, Forms0 (recC D0 sc 1 Lc I ψ hd) u)
    (B : GL (Fin D0.R.k) D0.host.E)
    (hBs : Cmp.StdB (recC D0 sc 1 Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D0.host.F)) (h : ((D0.what₂.places.resChar w : ℕ) : 𝓞 D0.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D0.host.F) (w'.adicCompletion D0.host.F))) B)
    (iK : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      KfRec D0 w (nFr D0 (D0.what₂.places.resChar w)) →+* ℂ_[D0.what₂.places.resChar w])
    (lam : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D0.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D0.what₂.LL), iK u w hg (embRec D0 w (nFr D0 (D0.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D0.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D0 Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (CH : CmpHyp0P T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB))
    (eq : (⟨D, Gt, c⟩ : Σ D : D7, GatTies D × LatCmp D) =
      ⟨recC D0 sc 1 Lc I ψ hd, gatTiesC D0 sc 1 Lc I ψ hd,
      Cmp.latCmpC T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB)
        (CH.toHyp0 fun u w hg v s x => pos_C D0 sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x).toHyp⟩)
    : IsRecC D Gt c

theorem gTiedAll_of_isRecC {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsRecC D Gt c) : Nonempty (GroupCompatibilityAll D Gt c) := by
  obtain ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨groupCompatibilityOfRecursion D0 sc 1 Lc I ψ hd H0 hL T B hBs hB (CH.toHyp0 fun u w hg v s x => pos_C D0 sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x).toHyp fun u w h => isHyperbolicAt_rec_of_placeIdentification D0 u w h (I u w h)⟩

def IsRecCEv : FamClass := fun Fm =>
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (hx : Fm.x1 < x), IsRecC (Fm.D x i) (Fm.gatT x i) (Fm.ex x hx i).cmp

def IsRecCF : FamClass := fun Fm => ∀ x i (hx : Fm.x1 < x), IsRecC (Fm.D x i) (Fm.gatT x i) (Fm.ex x hx i).cmp

end Formalism.L2.G

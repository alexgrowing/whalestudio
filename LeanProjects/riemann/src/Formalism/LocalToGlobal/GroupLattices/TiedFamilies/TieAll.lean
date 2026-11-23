import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieExC
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLatFin
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

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
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)

structure CmpLeft : Prop where
  same : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u
  blk : ∀ u w hg, BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B
  psi0 : ∀ u, LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u
  chi : ∀ u w hg i (γ : (((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap ((recC D sc Ce Lc I ψ hd).gat u w hg).O ((recC D sc Ce Lc I ψ hd).gat u w hg).Kf
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).χ γ : ((recC D sc Ce Lc I ψ hd).gat u w hg).O) *
          (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg r = 1
  valInt : ValIntRec T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB)

variable {D sc Ce Lc I ψ hd H0 hL T B hBs hB}

set_option maxHeartbeats 8000000 in

theorem CmpLeft.core (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpCore T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) where
  same := N.same
  ex := fun u w hg => ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u (N.same u) w hg
    (evRatRep_rec T (gatTiesC D sc Ce Lc I ψ hd) u w hg B (N.blk u w hg)) (N.psi0 u)
  pos := pos
  chi := N.chi

set_option maxHeartbeats 8000000 in

theorem CmpLeft.toHyp0P (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpHyp0P T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) :=
  cmpHyp0P_of_cmpCore (N.core pos)
    (fun u w hg => gatIs_recC D sc Ce Lc I ψ hd H0 hL (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg) N.valInt

end Formalism.L2.G

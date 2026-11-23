import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtC
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

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

set_option maxHeartbeats 8000000 in

theorem ptOne_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    PtOne ((T u).cls0).lev ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) :=
  ptOne_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u hU w hg B (frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg)
    (hypT_C D sc Ce Lc I ψ hd H0 hL u w hg)

set_option maxHeartbeats 8000000 in

theorem ex_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : EvRatRep (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u))
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T (gatTiesC D sc Ce Lc I ψ hd)
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) u w hg
    (ptOne_C D sc Ce Lc I ψ hd H0 hL T B hB u hU w hg) h1 h2

set_option maxHeartbeats 8000000 in

theorem ex_C_blk (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B)
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u hU w hg
    (evRatRep_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T
      (gatTiesC D sc Ce Lc I ψ hd) u w hg B h1) h2

end Formalism.L2.G

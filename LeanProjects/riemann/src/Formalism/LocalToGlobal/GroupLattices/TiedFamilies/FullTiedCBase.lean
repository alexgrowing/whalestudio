import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.LocPackC
import Formalism.LocalToGlobal.GroupLattices.TiedRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.LatticeComparisonCompatible

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def levTieOf {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    Formalism.L2.Herm.GLevTie L' G :=
  h ▸ t

theorem levTieOf_fr {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).fr = t.fr := by
  subst h
  rfl

theorem levTieOf_spl {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).spl = t.spl := by
  subst h
  rfl

end Cast

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)

def packC : ∀ u (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LocPack D u (Lc u) (D.what₂.places.resChar w) :=
  fun u w h => locPackC D u (Lc u) w h.2.1 (nFr_spec D h).1 (nFr_spec D h).2 (I u w h) (ψ u w h)

variable (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev recC : D7 := recG D sc Ce Lc (packC D Lc I ψ) hd

abbrev gatTiesC : GatTies (recC D sc Ce Lc I ψ hd) := gatTiesG D sc Ce Lc (packC D Lc I ψ) hd

set_option maxHeartbeats 4000000 in

theorem ringTied_recC (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin ((recC D sc Ce Lc I ψ hd).gat u w hg).P.nV) : RingCompatibleAt (recC D sc Ce Lc I ψ hd) u w hg v := by
  unfold RingCompatibleAt
  exact ⟨RingEquiv.refl (((recC D sc Ce Lc I ψ hd).gat u w hg).P.W v),
    RingEquiv.refl (((recC D sc Ce Lc I ψ hd).gat u w hg).P.Qq v),
    RingEquiv.refl ((recC D sc Ce Lc I ψ hd).gat u w hg).O, RingEquiv.refl ((recC D sc Ce Lc I ψ hd).gat u w hg).Kf,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

def hermitianLevelZeroOfRecursion (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u) :
    Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd) :=
  { H0 with g := fun u w hg => levTieOf (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg) }

theorem fullTiedC_base (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u) :
    (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).lev0 = H0.lev0 := rfl

theorem gatIs_recC (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (hH : ∀ u w h, Cmp.HypAtP (I u w h)) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GatIs (recC D sc Ce Lc I ψ hd) (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).lev0 u w hg := by
  exact gatIs_recG D sc Ce Lc (packC D Lc I ψ) hd _ hL hH u w hg

set_option maxHeartbeats 4000000 in

theorem frRat_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Cmp.FrRat (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B := by
  intro w' h
  dsimp only [hermitianLevelZeroOfRecursion]
  erw [levTieOf_fr (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg),
    levTieOf_spl (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg)]
  exact hB u w hg w' h

set_option maxHeartbeats 4000000 in

def cmpInC (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) :
    Cmp.CmpIn (recC D sc Ce Lc I ψ hd) (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) where
  embW := fun _ w _ => embRec (recC D sc Ce Lc I ψ hd) w (nFr D (D.what₂.places.resChar w))
  embW_int := fun _ w _ x => embRec_int (recC D sc Ce Lc I ψ hd) w (nFr D (D.what₂.places.resChar w)) x
  B := B
  B_std := hBs
  fr_B := fun u w hg => frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg

set_option maxHeartbeats 4000000 in

def groupCompatibilityOfRecursion (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (CH : Cmp.CmpHyp T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB))
    (hH : ∀ u w h, Cmp.HypAtP (I u w h)) :
    GroupCompatibilityAll (recC D sc Ce Lc I ψ hd) (gatTiesC D sc Ce Lc I ψ hd)
      (Cmp.latCmpC T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) CH) where
  herm := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL
  forms := T
  cmp := Cmp.latticeComparisonCompatible T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) CH
  ring := ringTied_recC D sc Ce Lc I ψ hd
  gat := gatIs_recC D sc Ce Lc I ψ hd H0 hL hH

end Formalism.L2.G

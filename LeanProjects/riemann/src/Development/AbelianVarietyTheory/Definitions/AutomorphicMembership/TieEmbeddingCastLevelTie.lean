import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
import Formalism.LocalToGlobal.GroupLattices.TiedRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

abbrev extMap := @Formalism.L2.G.ExtOf.map

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

theorem extMap_φ (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (x : Os) :
    (X.map eO eK hc hfrac hcomp).φ x = eO (X.φ x) := rfl

theorem extMap_φK (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (y : Ks) :
    (X.map eO eK hc hfrac hcomp).φK y = eK (X.φK y) := rfl

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

abbrev AllTies := @Formalism.L2.G.GroupCompatibilityAll

abbrev castLevelTie := @Formalism.L2.G.levTieOf

abbrev tieEmbedding := @Formalism.L2.G.tieIw

abbrev hermTies := @Formalism.L2.G.hermitianLevelZeroOfRecursion

abbrev comparisonData := @Formalism.L2.G.cmpInC

abbrev recordAllTies := @Formalism.L2.G.groupCompatibilityOfRecursion

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias castLevelTie_basis := Formalism.L2.G.levTieOf_fr

alias castLevelTie_splitting := Formalism.L2.G.levTieOf_spl

alias tieEmbedding_castLevelTie := Formalism.L2.G.tieIw_levTieOf

alias ringTie_record := Formalism.L2.G.ringTied_recC

alias hermTies_level := Formalism.L2.G.fullTiedC_base

alias localIs_record := Formalism.L2.G.gatIs_recC

alias hermTies_basis_rational := Formalism.L2.G.frRat_C

alias comparison_embedding_eq := Formalism.L2.G.locAt_iw_C

alias comparison_positions := Formalism.L2.G.pos_C

end Ties

section Bridge

theorem frobOrder_eq (D : D7) (p : ℕ) : frobOrder D p = nFr D p := rfl

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

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

theorem packAll_eq : packAll D Lc I ψ = packC D Lc I ψ := by
  funext u w h
  exact pack_eq D u (Lc u) w h.2.1 (nFr_spec D h).1 (nFr_spec D h).2 (I u w h) (ψ u w h)

theorem record_eq (hd' : ∀ u w h, ((packAll D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0) :
    record D sc Ce Lc I ψ hd' = recC D sc Ce Lc I ψ hd := by
  have key : ∀ X X' (_ : X = X') h h', recG D sc Ce Lc X h = recG D sc Ce Lc X' h' := by
    intro X X' e h h'
    subst e
    rfl
  exact key _ _ (packAll_eq D Lc I ψ) hd' hd

theorem recordAllTies_level (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B) (hB) (CH) (hH) (u : D.what₂.Word) :
    (groupCompatibilityOfRecursion D sc Ce Lc I ψ hd H0 hL T B hBs hB CH hH).herm.lev0 u = Lc u := hL u

theorem recordAllTies_forms (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B) (hB) (CH) (hH) :
    (groupCompatibilityOfRecursion D sc Ce Lc I ψ hd H0 hL T B hBs hB CH hH).forms = T := rfl

example : Joints.StdSubAt (recC D sc Ce Lc I ψ hd) :=
  standardSub_of_ringTie _ (ringTie_record D sc Ce Lc I ψ hd)

example (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocalIs (recC D sc Ce Lc I ψ hd) Lc u w hg :=
  localIs_of_hyperspecial D sc Ce Lc (packC D Lc I ψ) hd Lc (fun _ => rfl)
    (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

alias IsConcrete.intro := Formalism.L2.G.IsRecC.intro

theorem IsConcrete.nonempty_allTies {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) :
    Nonempty (GroupCompatibilityAll D Gt c) :=
  gTiedAll_of_isRecC h

theorem AllTies.standardSub {D : D7} {Gt : GatTies D} {c : LatCmp D} (G : AllTies D Gt c) : Joints.StdSubAt D :=
  standardSub_of_ringTie D G.ring

theorem IsConcrete.ringTie {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV) :
    RingTie D u w hg v :=
  h.nonempty_allTies.elim fun G => G.ring u w hg v

example {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {v : Fin (D.gat u w hg).P.nV} (h : RingTie D u w hg v) :
    Nonempty (WQ (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).P.W v) :=
  h.elim fun e _ => ⟨e⟩

example {D : D7} {Gt : GatTies D} {c : LatCmp D} : IsConcrete D Gt c ↔ IsRecC D Gt c := Iff.rfl

end GlobalTheory.Mem.LocalPack

import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_conj {D : D7} (x : D.host.E) : star x = D.host.conj x := bridge_star_holds D.R D.host x

def toErrX {D : D7} (X : FullTied D) : ErrX D where
  piG := (X.levelZeroCompatibility D.u₀).piG
  piG_K := (X.levelZeroCompatibility D.u₀).piG_K
  piG_norm := fun i => by rw [← star_conj]; exact (X.levelZeroCompatibility D.u₀).piG_norm i
  piT := fun u => (X.atT u).piU
  piT_K := fun u => (X.atT u).piU_K
  piT_norm := fun u => (X.atT u).piU_norm
  piT_cong := fun u => (X.atT u).piU_cong
  vPl := fun u v => (X.base.vT u v).1
  vPl_inj := fun u a b h => (X.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal := fun u v => (X.base.vT u v).2

theorem piGLevel {D : D7} (X : FullTied D) : PiGLevel D X.base.lev0 (toErrX X) := by
  simp only [PiGLevel]
  intro u i v h
  have e : (X.levelZeroCompatibility u).piG = (X.levelZeroCompatibility D.u₀).piG := X.piG u D.u₀
  have k := (X.levelZeroCompatibility u).splitG_pi i v h
  rw [e, star_conj] at k
  exact k

theorem piTLevel {D : D7} (X : FullTied D) : PiTLevel D X.base.lev0 (toErrX X) := by
  simp only [PiTLevel]
  intro u v z hz y
  exact (X.levelZeroCompatibility u).fM_pi _ _ z hz y

def GroupCompatibleAtPlaces (D : D7) (H : HermTied D) (G : GTied D H) (Gt : GatTies D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
    x ∈ ((G u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w
        (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GIwTied {D : D7} (H : HermTied D) (G : GTied D H) {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (x : D.host.E),
    (G u w hg).eQ v _ rfl (Kp.iw 0 v x) =
      ((G u w hg).spl _ ((G u w hg).pl v).2
        (inclE (F := D.host.F) (((G u w hg).pl v).1.adicCompletion D.host.F) x)).1

def GIwPos {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) (Kp.iw 0 v x)) =
      c.embW u w hg (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (if s.val % 2 = 1 then D.host.conj x else x))

structure JoinTied {D : D7} (X : FullTied D) (lev : LevelData D) (eX : ErrX D) (Gt : GatTies D) : Prop where
  lev_eq : lev = X.base.lev0
  errX_eq : eX = toErrX X
  gpl : GroupCompatibleAtPlaces D X.base X.g Gt

structure ExtraTied {D : D7} (X : FullTied D) {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop where
  join : JoinTied X ex.lev ex.errX hT
  iw : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwTied X.base X.g u w h (ex.ker u w h)
  iw_pos : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwPos u w h (ex.ker u w h)

theorem JoinTied.piG_lev {D : D7} {X : FullTied D} {lev : LevelData D} {eX : ErrX D} {Gt : GatTies D}
    (J : JoinTied X lev eX Gt) : PiGLevel D lev eX := by
  obtain ⟨h1, h2, _⟩ := J
  subst h1
  subst h2
  exact piGLevel X

theorem JoinTied.piT_lev {D : D7} {X : FullTied D} {lev : LevelData D} {eX : ErrX D} {Gt : GatTies D}
    (J : JoinTied X lev eX Gt) : PiTLevel D lev eX := by
  obtain ⟨h1, h2, _⟩ := J
  subst h1
  subst h2
  exact piTLevel X

end Formalism.L2.Herm

end

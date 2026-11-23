import Formalism.SharpRestriction.InertJacobiLevels.ExtraNew
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.SharpRestriction.InertJacobiLevels.ResCharConj
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
import Formalism.SharpRestriction.InertJacobiLevels.ExtraEnt
import Formalism.LocalRingCardinality.DataMink

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure Shape (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  gatM : ∀ u w h, (D.gat u w h).M = ⊥
  gatComp : ∀ u w h, Nonempty ((D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
  gatTr : ∀ u w h (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
    (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L

structure LevErr (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  seen : SeenDef D errX
  tauOf : TauOfDef D errX

def GaugeExists {R : Ranks} (H : Host R) (sp : @Spaces R H.F H.E _ _ _ _ H.cmStar _) : Prop :=
  letI := H.cmStar
  ∃ G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam H.F H.E sp.cm.sig, G.IsGauge

structure ExtraIn (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (X : DivX D) (cX : ExtraC) where
  shape : Shape D

  mjH : ∀ j, Subsingleton (X.MjH j).V
  kapR : X.kapR D.what₂.embLL = 1

  compS : ∀ u w h j, IsEmpty ((Gl.Lv u w h).compS j)
  vram : ∀ u w h, Gl.Vram u w h = ⊥
  latTied : G.LatTied hT Gi Gl

  ep_def : G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : G.KapIDef Gi K
  fills_all : FillsAll hT Gl
  fdef : L.FDef

  kap_def : DV.KapDef D
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  cover : NTw.TwCover D.ntw

  le : LevErr D
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h
  gauge : GaugeExists D.host D.sp

  large : cX.err.Large
  edef : L.EDef le.errX K cX.err

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D}
  {K : G.Consts} {X : DivX D} {cX : ExtraC}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def extraOf (I : ExtraIn D L hT Gi Gl K X cX) : Extra D L hT Gi Gl K X cX :=
  haveI := I.shape.mult
  haveI := I.shape.mtL
  haveI := I.shape.mj
  haveI := I.shape.ee0
  haveI := I.shape.nu
  haveI := I.shape.lat
  haveI := I.shape.yTw
  haveI := I.shape.mtV
  haveI := I.shape.fmN
  haveI := I.mjH
  haveI := I.shape.clsTw
  haveI := I.shape.loc
  { lev := I.le.lev
    th := thetaZero D
    th_io := thetaZero_io D
    cmp := latCmpZero D I.shape.gatM I.served
    lat := latDefsZero D I.shape.gatM I.served Gi Gl K I.vram
    tw := twFormsZero D
    ker := fun u w h =>
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      haveI := I.shape.clsTw u (D.what₂.muAt w)
      haveI := I.compS u w h
      kerZeroE D hT I.shape.gatM I.served (twFormsZero D) (plEmb D) u w h (Gl.Ch u w h) (I.latTied u w h).2.1 (I.latTied u w h).1
        (I.shape.gatComp u w h).some (I.shape.gatTr u w h) (exists_latTup _)
    ep_def := I.ep_def
    ep_tie := I.ep_tie
    kapI_def := I.kapI_def
    fills_all := I.fills_all
    nu_unserved := nuUnserved_zero Gi K
    idx := idxDefs_zero D X I.shape.Ij0 I.shape.jw0
    kap_def := I.kap_def
    lam_def := lamDef_zero D
    kapR_def := kapRBase_zero X I.shape.drows I.kapR
    errX := I.le.errX
    err := ⟨I.large, I.le.piG_lev, I.le.piT_lev, I.le.seen, I.le.tauOf, dGamDef_of D I.shape.dgam, I.edef⟩
    nch := nchZero D (nchEmbOf D I.shape.ll0 I.cover)
    nch_tie := nchTie_zero D I.shape.ll0 I.cover
    xd := thDataZero D
    p0 := trivialSide D
    rationalRoots_def := trivialSide_rrDef_of_subsingleton D
    amb := haveI : ∀ μ, Subsingleton ((RowSide.sharp D).Amb μ) := I.shape.amb; ambZero D _
    amb0 := ambZero D _
    fdef := I.fdef
    duStar_def := I.duStar_def
    Dstar_def := I.Dstar_def
    gauge := I.gauge.choose
    gauge_def := I.gauge.choose_spec }

end Formalism.MainNotions.Inhab

end

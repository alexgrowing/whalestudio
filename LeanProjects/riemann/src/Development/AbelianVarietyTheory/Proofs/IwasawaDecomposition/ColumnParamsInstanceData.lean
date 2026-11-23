import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.TwistedScalarIndependence

theorem dep_imp {α : Sort _} {β : α → Sort _} (P : ∀ a, β a → Prop) {a a' : α} {b : β a} {b' : β a'} (h : a' = a) (hb : HEq b' b)
    (H : P a b) : P a' b' := by
  subst h
  cases hb
  exact H

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Field

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
  (lam : type_of% R.lam3) (err : type_of% R.err0)

abbrev newR : RealDat3 D A3 Ks := (R.updS R.kap lam).withErr err

variable {R F} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}

set_option maxHeartbeats 4000000 in

def newC (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) X0 Y) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) :
    ReadC (newR R lam err) (reFace F Dc Sp Zsc) X0 Y' where
  wU := (by with_unfolding_all exact (C₀.wU :))
  bij := (by with_unfolding_all exact (C₀.bij :))
  eNu := (by with_unfolding_all exact (C₀.eNu :))
  NuC := (by with_unfolding_all exact (C₀.NuC :))
  nu := (by with_unfolding_all exact (C₀.nu :))
  pt := by
    have h := dep_imp (β := fun tup : T → D.what₂.Tup =>
        ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t))
      (fun tup jA => ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (zsOf R F)).a (C₀.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (zsOf R F)).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (zsOf R F)).Pt (C₀.wU u) t x f) =
          D.what₂.perCol u (tup t) (D.jN u (C₀.eNu u x)) (jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)))
      (b := Y.jA) (b' := (by with_unfolding_all exact (Y'.jA :))) ht ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (C₀.pt :)))
    kexactB h

set_option maxHeartbeats 4000000 in

theorem rationalFormsComparison_baseLevel_indep_scalars {a0 : AmbForm D X0.s} (h : ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J) (ht : Y'.tup = Y.tup)
    (hj : HEq Y'.jA0 Y.jA0) :
    ∃ J, AmbTie D A3.A X0.s a0 (reFace F Dc Sp Zsc).P0 (reFace F Dc Sp Zsc).ψ0 Y'.tup Y'.jA0 J := by
  have h' := dep_imp (β := fun tup : T → D.what₂.Tup =>
      ∀ t, (Fin (rDim D A3.A F.P0 F.ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t))
    (fun tup jA => ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 tup jA J) (b := Y.jA0) (b' := (by with_unfolding_all exact (Y'.jA0 :))) ht ((by with_unfolding_all exact (hj :))) h
  exact (by with_unfolding_all exact (h' :))

set_option maxHeartbeats 4000000 in

theorem mj_new {Z : ReadL R F X0 Y} {Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) X0 Y'} {Xd : DivX D} (h : MjAre Z Xd)
    (hj : HEq Z'.jW Z.jW) : MjAre Z' Xd := by
  obtain ⟨J, hJ⟩ := h
  have e : Z'.jW = (by with_unfolding_all exact (Z.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj :)))
  refine ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ?_, (by with_unfolding_all exact (hJ.hlat :))⟩
  rewrite [e]
  exact (by with_unfolding_all exact (hJ.j_eq :))

end Field

set_option maxHeartbeats 4000000 in

def newGeo {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) :
    GlobalTheory.RealGeo.GeoHalf C (GlobalTheory.RealGeo.Upd.upE C R.toRealDat R.kap R.lam err) fun _ => 1 :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R.toRealDat R.kap R.lam err g.fw, g.bar,
    fun i => GlobalTheory.RealGeo.Upd.updO C R.toRealDat R.kap R.lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE R.kap R.lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩

set_option maxHeartbeats 4000000 in

theorem inGeo_new {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (newGeo lam err g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

section Tw

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
  {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (lam : type_of% R.lam3) (err : type_of% R.err0)
  {Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0} {Z : ReadL R F ex.p0 Y}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 ex.p0}

set_option maxHeartbeats 4000000 in

def newTw (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG) (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J) (hM : MjAre Z Yd)
    (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) : TwIn ex where
  G := G
  Pl0 := Pl0
  I0 := I0
  T := T
  A3 := A3
  core := C
  R := newR R lam err
  F := reFace F Dc Sp Zsc
  cG := cG
  geo := (by with_unfolding_all exact ((newGeo lam err g) :))
  pins := hP
  err := hE
  Y := Y'
  Z := Z'
  C := newC lam err C₀ ht hj
  sEE := kc% sEE
  div := (GlobalTheory.T.divisionCompatible_at_readIdentifications hC D G Pl0 I0 T A3 C.Q.c.F (newR R lam err) (reFace F Dc Sp Zsc) cG ex.p0 Y' Z' (newC lam err C₀ ht hj)
    (kc% sEE) Yd (mj_new lam err hM hW).choose hP hH (fun _ _ => (by with_unfolding_all exact (hG :)))).1
  JA := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose
  amb0 := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose_spec
  JM := (mj_new lam err hM hW).choose
  mjH := (mj_new lam err hM hW).choose_spec

end Tw

end GlobalTheory.Mem.R3.TwistedScalarIndependence

namespace GlobalTheory.Mem.R3

open TwistedScalarIndependence

set_option maxHeartbeats 8000000 in

theorem twArgs_exists : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  intro hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp Dc Sp₀ Zsc₀ C₀ Sp Zsc sEE
  obtain ⟨kap, lam, err, hP, hH, hE, rfl, hl, Y', Z', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    GlobalTheory.T.reFace_zero_part_conventions_chosen_again (w.st Z).toD7 _ _ _ _ (famT t) _ t.r.z.R t.r.z.F t.r.z.cG ex.p0 t.r.Y t.r.Z Dc Sp Zsc t.r.z.pins t.r.intersectionNumber_baseChange hp
  let x : TwIn ex := newTw (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG) (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp)
    (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' ((by with_unfolding_all exact (C₀ :))) sEE hP hH hE hG hA.2 hM h1 h3 h4 h13
  let a : TwArgs ex t :=
    { Dc := Dc, Sp := Sp, Zsc := Zsc, lam := lam, err := err, lam_eq := hl, x := x
      pack := rfl
      intersectionNumber_baseChange := (by with_unfolding_all exact (hH :))
      κ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.κ) :))
      v₀ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.v₀) :))
      fw := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.fw.e) :))
      tup := (by with_unfolding_all exact ((heq_of_eq h1) :))
      tupT := (by with_unfolding_all exact ((heq_of_eq h2) :))
      jA := (by with_unfolding_all exact (h3 :))
      jA0 := (by with_unfolding_all exact (h4 :))
      eMt := (by with_unfolding_all exact (h5 :))
      PY := (by with_unfolding_all exact (h6 :))
      PW := (by with_unfolding_all exact (h9 :))
      eFT := (by with_unfolding_all exact (h7 :))
      IL := (by with_unfolding_all exact (h8 :))
      eE := (by with_unfolding_all exact (h10 :))
      eW := (by with_unfolding_all exact (h11 :))
      jW := (by with_unfolding_all exact (h13 :))
      eRR := (by with_unfolding_all exact (h12 :)) }
  refine ⟨a, rfl, HEq.rfl, rfl, ?_, ?_, ?_, ?_⟩
  · kexactB HEq.refl sEE
  · kexactB HEq.refl C₀.wU
  · kexactB HEq.refl C₀.eNu
  · exact (by with_unfolding_all exact (inGeo_new lam err t.inGeo :))

end GlobalTheory.Mem.R3

end

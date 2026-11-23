import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BaseRestrict

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseA (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) : FamIn D.what₂.LL G Pl0 Unit D.R.m := A.comap (fun _ : Unit => A.μ0) ()

def baseF (F : Face D A) : Face D (baseA A) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def baseR (R : RealDat D A Ks) : RealDat D (baseA A) Ks :=
  R.comap (fun _ : Unit => A.μ0) () (fun _ => ()) R.twPl R.FW R.kap (fun i _ => R.lam i A.μ0) R.err0

variable {R : RealDat D A Ks}

set_option maxHeartbeats 2000000 in
theorem core_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.Hk3.Core (baseR R) (baseF F) := by
  obtain ⟨hlev, hgrp, hfam, hmod, hch, hth⟩ := h
  refine ⟨LevCh.comap_is hlev (f := fun _ : Unit => A.μ0) (fun _ _ _ => rfl) rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ q => hgrp.red_R A.μ0 q, fun i _ q => hgrp.red_L i A.μ0 q, hgrp.levels, hgrp.record, hgrp.chiW⟩
  · obtain ⟨g, c0R, c0L, ht⟩ := hfam.tie
    exact ⟨⟨g, c0R, c0L, ht.comap (fun _ : Unit => A.μ0) ()⟩, hfam.Sb, fun _ PP => hfam.roots A.μ0 PP, hfam.pl_onto,
      fun _ P => hfam.degR A.μ0 P, fun i _ P => hfam.degL i A.μ0 P, fun i _ P hP => hfam.muVal i A.μ0 P hP,
      fun P hP => hfam.etaVal P hP⟩
  · exact ⟨hmod.inf, hmod.vpos, hmod.cX, hmod.cV, hmod.prX, fun _ => hmod.HX A.μ0, fun i _ => hmod.HV i A.μ0, hmod.HE, hmod.HW,
      hmod.gE, hmod.gW, fun _ x => hmod.jX A.μ0 x, fun i _ x => hmod.jV i A.μ0 x, fun _ j h2 => hmod.νY A.μ0 j h2,
      fun _ => hmod.νY' A.μ0, hmod.ν0, fun _ => hmod.νX A.μ0, fun i _ => hmod.νV i A.μ0, hmod.νW, hmod.BV, hmod.order⟩
  · exact ⟨fun _ k hk => hch.ωY A.μ0 k hk, fun _ => hch.ωX A.μ0, fun _ k hk => hch.vY A.μ0 k hk, fun _ => hch.vX A.μ0,
      fun _ k hk P => hch.ptY A.μ0 k hk P, fun _ P => hch.ptX A.μ0 P, fun _ k hk => hch.ItY A.μ0 k hk, fun _ => hch.ItX A.μ0,
      fun _ => hch.ioY A.μ0, fun _ => hch.ioX A.μ0, fun _ => hch.Th A.μ0⟩
  · exact ⟨fun i _ => hth.ωP i A.μ0, fun i _ => hth.vP i A.μ0, fun i _ P => hth.pt_theta i A.μ0 P, fun i _ => hth.ioP i A.μ0,
      fun i _ => hth.thF_mem i A.μ0, fun i _ => hth.thF i A.μ0, fun i _ => hth.thG i A.μ0⟩

theorem ioExt_base (h : IoExt R) : IoExt (baseR R) := h

theorem qGuard_base (h : QGuard R) : QGuard (baseR R) := ⟨fun _ => h.1 A.μ0, fun _ => h.2 A.μ0⟩

theorem baseOf_base {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (baseR R) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

theorem twLev_base {χ : Formalism.L2.Host.HChar D.host.E} {xi : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)}
    {xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TwConj.TwLev R χ xi Q xiR) : TwConj.TwLev (baseR R) χ xi Q xiR :=
  ⟨h.xi, h.xi_fin, h.xi_triv, h.xi_tame, h.Q_pl, h.Q_off,
    fun p hp => (h.Q_de p hp).imp fun _ h' => ⟨fun _ => h'.1 A.μ0, h'.2⟩,
    h.Q_ram, h.xiR, h.roots, h.muVal, h.half, h.guard⟩

end Any

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 2000000 in

def fwBase (t : FWTie T R κ v₀) : FWTie T (baseR R) κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := t.chiR
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev

set_option maxHeartbeats 2000000 in

def omBase {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (baseR R) i Unit (fun _ => (baseA A).μ0) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := O.dδ
  Cl' := O.Cl'
  fCl := O.fCl
  bad := O.bad
  Lh := O.Lh
  La := O.La
  Nc := O.Nc
  gam := O.gam
  vol := O.vol
  ep := O.ep
  B := O.B
  epF := O.epF
  io := O.io
  hw := O.hw
  φ := O.φ
  w := O.w
  U₂ := O.U₂
  dict₂ := O.dict₂
  xi := O.xi
  thAd := O.thAd
  Plc := O.Plc

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 4000000 in
theorem omPins_base {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : OMPins T (baseR R) κ v₀ (fun i => omBase (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', h3.comap (fun _ : Unit => A.μ0) (), h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_base {i : Fin D.R.m} (cc ph) :
    (omBase (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_base {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (baseR R) κ v₀ (fun i => omBase (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_base _ _).2 (h ⟨cc, p, (oneMapOf_base _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem ext_base (j : Fin D.R.m) : TwConj.Ext T R κ v₀ O j (baseR R) v₀ (fun i => omBase (O i)) :=
  ⟨fun _ h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

set_option maxHeartbeats 2000000 in

theorem restrict_to_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∃ (A0 : FamIn D.what₂.LL G Pl0 Unit D.R.m) (R0 : RealDat D A0 T.Q.c.F) (F0 : Face D A0)
      (v0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R0.MW i σ).Vec) (O0 : ∀ i, OMDat T.toCore R0 i Unit (fun _ => A0.μ0)),
      GlobalTheory.BigOn.Exp.TwConj.Laws T R0 F0 κ v0 O0 ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R0 v0 O0 ∧ (∀ t, R0.xiH t = 1) ∧
      ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
        GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → GlobalTheory.BigOn.Exp.TwConj.TwLev R0 χ xi Q xiR := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B h
  obtain ⟨h1, -, ⟨h3⟩, h4, h5, h6, h7, h8⟩ := h
  exact ⟨baseA A, baseR R, baseF F, v₀, fun i => omBase (O i),
    ⟨core_base h1, inferInstance, ⟨fwBase h3⟩, ioExt_base h4, qGuard_base h5, omPins_base h6, phaseTie_base h7, baseOf_base h8⟩,
    ext_base j, fun _ => h1.lev.xi_base, fun _ _ _ _ h => twLev_base h⟩

end GlobalTheory.BaseRestrict

end

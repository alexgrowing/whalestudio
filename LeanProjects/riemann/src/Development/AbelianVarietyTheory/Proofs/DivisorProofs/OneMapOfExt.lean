import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type}

structure NewLev (D : D7) (N : Type) where
  xiH : N → Formalism.L2.Host.HChar D.host.E
  xi : N → (AE D)ˣ →* Circle
  Q : N → Finset (Pl D.host.E)
  xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ

def NewLev.ofTuples (L : LevCh D T) (s : N → T) : NewLev D N :=
  ⟨fun n => L.xiH (s n), fun n => L.xi (s n), fun n => L.Q (s n), fun n => L.xiR (s n)⟩

def extL (L : LevCh D T) (V : NewLev D N) : LevCh D (T ⊕ N) :=
  { L with
    xiH := Sum.elim L.xiH V.xiH
    xi := Sum.elim L.xi V.xi
    Q := Sum.elim L.Q V.Q
    xiR := Sum.elim L.xiR V.xiR }

structure NewFam {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (N : Type) where
  ok : N → Set Pl0
  muVal : Fin m → N → Pl0 → Kˣ
  SR : N → CSD K
  actR : ∀ n, Representation K G (SR n).Forms
  opR : ∀ n, ok n × ℕ → Module.End K (SR n).Forms
  SL : Fin m → N → CSD K
  actL : ∀ j n, Representation K G (SL j n).Forms
  opL : ∀ j n, ok n × ℕ → Module.End K (SL j n).Forms

def extA {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (X : NewFam A N) :
    FamIn K G Pl0 (T ⊕ N) m where
  v0 := A.v0
  μ0 := .inl A.μ0
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j := Sum.elim (A.muVal j) (X.muVal j)
  etaVal := A.etaVal
  ok := Sum.elim A.ok X.ok
  MtildeCSD := Sum.elim A.MtildeCSD X.SR
  leftGroupActionRight τ := Sum.rec A.leftGroupActionRight X.actR τ
  heckeR τ := Sum.rec A.heckeR X.opR τ
  MtCSD j := Sum.elim (A.MtCSD j) (X.SL j)
  leftGroupActionLift j τ := Sum.rec (A.leftGroupActionLift j) (X.actL j) τ
  heckeL j τ := Sum.rec (A.heckeL j) (X.opL j) τ

theorem extA_comap {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m)
    (X : NewFam A N) : (extA A X).comap Sum.inl A.μ0 = A := rfl

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure NewReal (R : RealDat D A Ks) (V : NewLev D N) (X : NewFam A N) where
  BR : ∀ n, Bridge.SideReal D D.sp.X'
    (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (X.ok n)))
    (X.SR n) (X.actR n) (X.opR n) (fun i => i.2)
  BL : ∀ i n, Bridge.SideReal D (Vc D i)
    (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (X.ok n)))
    (X.SL i n) (X.actL i n) (X.opL i n) (fun i => i.2)
  HX : N → HMod (Bridge.Gf D.sp.X' → R.cX.W)
  HV : ∀ i, N → HMod (Bridge.Gf (Vc D i) → (R.cV i).W)
  jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H
  jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H
  νY : N → ∀ j, Measure (GA D (Yc D j))
  fdY : N → ∀ j, Set (GA D (Yc D j))
  νX : N → Measure (GA D D.sp.X')
  fdX : N → Set (GA D D.sp.X')
  νV : ∀ i, N → Measure (GA D (Vc D i))
  fdV : ∀ i, N → Set (GA D (Vc D i))
  ωY : N → ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)
  ωX : N → GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)
  ωP : ∀ i, N → GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)
  vY : N → ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : N → WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ
  vP : ∀ i, N → WO (Vc D i) (Wc D i) → ℂ
  ioY : ∀ n k, MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) ((extL R.toLevCh V).datYt (.inr n) (k + 1) R.triv))
      (Lev.levChi _ (R.βY (k + 1)) ((extL R.toLevCh V).datYt (.inr n) (k + 1) R.triv)) →ₗ[ℂ]
    MultT R.θ (R.MY k) (levS _ (R.βY k) ((extL R.toLevCh V).datYt (.inr n) k R.triv))
      (Lev.levChi _ (R.βY k) ((extL R.toLevCh V).datYt (.inr n) k R.triv))
  ioX : ∀ n, LinearMap.range (R.cX.toMap R.prX ∘ₗ (HX n).e) →ₗ[ℂ]
    MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) ((extL R.toLevCh V).datYt (.inr n) (D.R.m - 1) R.triv))
      (Lev.levChi _ (R.βY (D.R.m - 1)) ((extL R.toLevCh V).datYt (.inr n) (D.R.m - 1) R.triv))
  Th : ∀ n, (HX n).H →ₗ[ℂ] R.HE.H
  thF : ∀ i n, (HV i n).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))
  thG : ∀ i n, (HV i n).H →ₗ[ℂ] (R.HW i (sg0 D A)).H

set_option maxHeartbeats 4000000 in

def extR (R : RealDat D A Ks) {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X) : RealDat D (extA A X) Ks where
  toLevCh := extL R.toLevCh V
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := { R := fun τ => Sum.rec R.B.R Y.BR τ, L := fun i τ => Sum.rec (R.B.L i) (Y.BL i) τ, rankR := R.B.rankR,
         rankL := R.B.rankL }
  prX := R.prX
  HX := Sum.elim R.HX Y.HX
  HV i := Sum.elim (R.HV i) (Y.HV i)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX τ := Sum.rec R.jX Y.jX τ
  jV i τ := Sum.rec (R.jV i) (Y.jV i) τ
  νY := Sum.elim R.νY Y.νY
  fdY := Sum.elim R.fdY Y.fdY
  ν0 := R.ν0
  fd0 := R.fd0
  νX := Sum.elim R.νX Y.νX
  fdX := Sum.elim R.fdX Y.fdX
  νV i := Sum.elim (R.νV i) (Y.νV i)
  fdV i := Sum.elim (R.fdV i) (Y.fdV i)
  νW := R.νW
  fdW := R.fdW
  ωY := Sum.elim R.ωY Y.ωY
  ωX := Sum.elim R.ωX Y.ωX
  ωP i := Sum.elim (R.ωP i) (Y.ωP i)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY := Sum.elim R.vY Y.vY
  vX := Sum.elim R.vX Y.vX
  vP i := Sum.elim (R.vP i) (Y.vP i)
  ItY := R.ItY
  ItX := R.ItX
  ioY τ := Sum.rec R.ioY Y.ioY τ
  ioX τ := Sum.rec R.ioX Y.ioX τ
  Th τ := Sum.rec R.Th Y.Th τ
  BV := R.BV
  ioP := R.ioP
  thF i τ := Sum.rec (R.thF i) (Y.thF i) τ
  thG i τ := Sum.rec (R.thG i) (Y.thG i) τ
  nW := R.nW
  FW := R.FW
  mu w := .inl (R.mu w)
  twPl := R.twPl
  kap := R.kap
  lam _ _ _ _ := 0
  err0 := R.err0

set_option maxHeartbeats 4000000 in
theorem extR_comap (R : RealDat D A Ks) {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X) :
    (extR R Y).comap Sum.inl A.μ0 R.mu R.twPl R.FW R.kap R.lam R.err0 = R := rfl

section Ties

variable {T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def extF (F : Face D A) (X : NewFam A N) : Face D (extA A X) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def TieExt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {V : NewLev D N}
    {X : NewFam A N} (Y : NewReal R V X) : Prop :=
  ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    Bridge.FamTie (extR R Y).B R.pl (R.Sb : Set (Pl D.host.E)) (extR R Y).Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

theorem ioExt_ext {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {V : NewLev D N}
    {X : NewFam A N} (Y : NewReal R V X) (h : IoExt R) : IoExt (extR R Y) := h

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {V : NewLev D N} {X : NewFam A N}
  (Y : NewReal R V X) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 2000000 in

def fwExt (t : FWTie T R κ v₀) : FWTie T (extR R Y) κ v₀ where
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

def omExt {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (extR R Y) i Unit (fun _ => (extA A X).μ0) where
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
theorem omPins_ext (hT : TieExt R Y) {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) :
    OMPins T (extR R Y) κ v₀ (fun i => omExt Y (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', hT _ _ _ h3, h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_ext {i : Fin D.R.m} (cc ph) :
    (omExt Y (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_ext {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (extR R Y) κ v₀ (fun i => omExt Y (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_ext Y _ _).2 (h ⟨cc, p, (oneMapOf_ext Y _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem fixBase_ext (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) : GlobalTheory.ConjTwist.FixBase T (extR R Y) i τ ↔ GlobalTheory.ConjTwist.FixBase T R i τ :=
  ⟨fun h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩⟩

end Ties

end GlobalTheory.TupExt

end

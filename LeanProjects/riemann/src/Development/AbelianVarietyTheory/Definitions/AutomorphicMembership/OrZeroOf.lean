import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}

def levCh (L : Formalism.IndefR.Links.LevCh D T) (f : T' → T) : Formalism.IndefR.Links.LevCh D T' where
  C := L.C
  xiH t := L.xiH (f t)
  mu0 := L.mu0
  eta := L.eta
  xi t := L.xi (f t)
  Pg := L.Pg
  Q t := L.Q (f t)
  chi := L.chi
  xiR t := L.xiR (f t)
  ΛY := L.ΛY
  ΛX := L.ΛX
  ΛV := L.ΛV
  ΛW := L.ΛW
  βY := L.βY
  βX := L.βX
  βV := L.βV
  βW := L.βW

theorem levCh_is {L : Formalism.IndefR.Links.LevCh D T} {f : T' → T} (hf : Function.Injective f) {μ : T'} (h : L.Is (f μ)) :
    (levCh L f).Is μ where
  mu0 := h.mu0
  eta := h.eta
  xi t := h.xi (f t)
  xi_inj := h.xi_inj.comp hf
  xi_base := h.xi_base
  xi_fin t := h.xi_fin (f t)
  xi_triv t := h.xi_triv (f t)
  xi_tame t := h.xi_tame (f t)
  Pg := h.Pg
  Q_pl t := h.Q_pl (f t)
  Q_off t := h.Q_off (f t)
  Q_de p hp := (h.Q_de p hp).imp fun _ h' t => h' (f t)
  Q_ram t := h.Q_ram (f t)
  chi := h.chi
  xiR t := h.xiR (f t)
  βY := h.βY
  βX := h.βX
  βV := h.βV
  βW := h.βW

section Two

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

set_option maxHeartbeats 2000000 in

def dat2 (R : RealDat D (A.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat D (A.comap f μ) Ks where
  toLevCh := levCh R.toLevCh f
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
  B := ⟨fun t => R.B.R (f t), fun i t => R.B.L i (f t), R.B.rankR, R.B.rankL⟩
  prX := R.prX
  HX t := R.HX (f t)
  HV i t := R.HV i (f t)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX t := R.jX (f t)
  jV i t := R.jV i (f t)
  νY t := R.νY (f t)
  fdY t := R.fdY (f t)
  ν0 := R.ν0
  fd0 := R.fd0
  νX t := R.νX (f t)
  fdX t := R.fdX (f t)
  νV i t := R.νV i (f t)
  fdV i t := R.fdV i (f t)
  νW := R.νW
  fdW := R.fdW
  ωY t := R.ωY (f t)
  ωX t := R.ωX (f t)
  ωP i t := R.ωP i (f t)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY t := R.vY (f t)
  vX t := R.vX (f t)
  vP i t := R.vP i (f t)
  ItY := R.ItY
  ItX := R.ItX
  ioY t := R.ioY (f t)
  ioX t := R.ioX (f t)
  Th t := R.Th (f t)
  BV := R.BV
  ioP := R.ioP
  thF i t := R.thF i (f t)
  thG i t := R.thG i (f t)
  nW := R.nW
  FW := R.FW
  mu := mu
  twPl := tw
  kap := R.kap
  lam i t := R.lam i (f t)
  err0 := R.err0

def bare2 (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) :
    Face D A where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat D (A.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem isGrp (h : R.IsGrp (bare2 _ P0 ψ0 P1 ψ1)) : (dat2 f μ R mu tw).IsGrp (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨fun t => h.red_R (f t), fun i t => h.red_L i (f t), h.levels, h.record, h.chiW⟩

set_option maxHeartbeats 2000000 in

theorem isFam (h : R.IsFam) : (dat2 f μ R mu tw).IsFam := by
  obtain ⟨g, c, l, ht⟩ := h.tie
  exact ⟨⟨g, c, l, ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq, ht.mapR, ht.mapL,
    fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, h.Sb, fun t => h.roots (f t), h.pl_onto, fun t => h.degR (f t),
    fun i t => h.degL i (f t), fun i t => h.muVal i (f t), h.etaVal⟩

set_option maxHeartbeats 2000000 in

theorem isModels (h : R.IsModels) : (dat2 f μ R mu tw).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, fun t => h.HX (f t), fun i t => h.HV i (f t), h.HE, h.HW, h.gE, h.gW, fun t => h.jX (f t),
    fun i t => h.jV i (f t), fun t => h.νY (f t), fun t => h.νY' (f t), h.ν0, fun t => h.νX (f t), fun i t => h.νV i (f t),
    h.νW, h.BV, h.order⟩

set_option maxHeartbeats 2000000 in

theorem exAt (e : R.ExAt) : (dat2 f μ R mu tw).ExAt :=
  ⟨fun k hk => (e.ItY k hk).imp fun _ h t => h (f t), e.ItX.imp fun _ h t => h (f t), fun t => e.ioY (f t), fun t => e.ioX (f t),
    fun t => e.Th (f t), fun i => (e.ioP i).imp fun _ h t => h (f t), fun i t => e.thF i (f t), fun i t => e.thG i (f t)⟩

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (h : p x) : OrZero p x :=
  ⟨fun _ => h, fun hn => absurd ⟨x, h⟩ hn⟩

set_option maxHeartbeats 2000000 in

theorem isChainW (h : R.IsChainW) (e : R.ExAt) : (dat2 f μ R mu tw).IsChainW :=
  ⟨fun t => h.ωY (f t), fun t => h.ωX (f t), fun t => h.vY (f t), fun t => h.vX (f t), fun t => h.ptY (f t), fun t => h.ptX (f t),
    fun k hk => orZero_of fun t => (h.ItY k hk).1 (e.ItY k hk) (f t), orZero_of fun t => h.ItX.1 e.ItX (f t),
    fun t => h.ioY (f t), fun t => h.ioX (f t), fun t => h.Th (f t)⟩

set_option maxHeartbeats 2000000 in

theorem isThPW (h : R.IsThPW) (e : R.ExAt) : (dat2 f μ R mu tw).IsThPW :=
  ⟨fun i t => h.ωP i (f t), fun i t => h.vP i (f t), fun i t => h.pt_theta i (f t),
    fun i => orZero_of fun t => (h.ioP i).1 (e.ioP i) (f t), fun i t => h.thF i (f t), fun i t => h.thG i (f t)⟩

theorem baseW (hf : Function.Injective f) (h : R.BaseW (bare2 _ P0 ψ0 P1 ψ1)) (e : R.ExAt) :
    (dat2 f μ R mu tw).BaseW (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨levCh_is hf h.lev, isGrp mu tw h.grp, isFam mu tw h.fam, isModels mu tw h.models, isChainW mu tw h.chain e, isThPW mu tw h.thP e⟩

end Two

end GlobalTheory.Mem.R3.Res

end

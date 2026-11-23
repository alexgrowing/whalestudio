import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem FamIn.comap_fam_R {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T' m) (f : T → T') (t0 : T) (t : T) :
    (A.comap f t0).fam.R t = A.fam.R (f t) := rfl

theorem FamIn.comap_fam_L {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T' m) (f : T → T') (t0 : T) (j : Fin m) (t : T) :
    (A.comap f t0).fam.L j t = A.fam.L j (f t) := rfl

theorem FamIn3.comap_rowI {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T' m) (f : T → T') (t0 : T) (t : T) :
    (A3.comap f t0).rowI t = A3.rowI (f t) := rfl

theorem FamIn3.comap_liftI {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T' m) (f : T → T') (t0 : T) (j : Fin m)
    (t : T) : (A3.comap f t0).liftI j t = A3.liftI j (f t) := rfl

end Formalism.L2.DIV

namespace Formalism.IndefR.Bridge

open Formalism.L2.Theta Formalism.L2.DIV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ}
  {A : FamIn D.what₂.LL G Pl0 T' m} {cR : CoefDat D D.sp.X'} {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
  {lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}

def FamReal.comap (B : FamReal D A cR cL lR lL) (f : T → T') (t0 : T) :
    FamReal D (A.comap f t0) cR cL (fun t => lR (f t)) (fun i t => lL i (f t)) where
  R t := B.R (f t)
  L i t := B.L i (f t)
  rankR := B.rankR
  rankL := B.rankL

theorem FamTie.comap {B : FamReal D A cR cL lR lL} {pl : Pl0 → Pl D.host.E} {S : Set (Pl D.host.E)}
    {Qt : T' → Finset (Pl D.host.E)} {tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)}
    {lamR : D.what₂.Tau → DomWeight D.sp.X'.rank} {lamL : ∀ (i : Fin m), D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank}
    {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
    {c0R : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W} {c0L : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W}
    (h : FamTie B pl S Qt tauL lamR lamL gramR c0R c0L) (f : T → T') (t0 : T) :
    FamTie (B.comap f t0) pl S (fun t => Qt (f t)) tauL lamR lamL gramR c0R c0L where
  ranks := h.ranks
  v0 := h.v0
  tauL_ok := h.tauL_ok
  pl_inj := h.pl_inj
  q := h.q
  S_fin := h.S_fin
  ok t P := h.ok (f t) P
  gramR_eq := h.gramR_eq
  mapR := h.mapR
  mapL := h.mapL
  coefR t := h.coefR (f t)
  coefL i t := h.coefL i (f t)

end Formalism.IndefR.Bridge

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comap

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

def LevCh.comap {T T' : Type} (L : LevCh D T') (f : T → T') : LevCh D T where
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

theorem LevCh.comap_is {T T' : Type} {L : LevCh D T'} {μ0 : T'} (h : L.Is μ0) {f : T → T'} (hf : Function.Injective f) {t0 : T}
    (h0 : f t0 = μ0) : (L.comap f).Is t0 where
  mu0 := h.mu0
  eta := h.eta
  xi t := h.xi (f t)
  xi_inj := h.xi_inj.comp hf
  xi_base := by
    show L.xiH (f t0) = 1
    rw [h0]; exact h.xi_base
  xi_fin t := h.xi_fin (f t)
  xi_triv t := h.xi_triv (f t)
  xi_tame t := h.xi_tame (f t)
  Pg := h.Pg
  Q_pl t := h.Q_pl (f t)
  Q_off t := h.Q_off (f t)
  Q_de p hp := by
    obtain ⟨P, hP⟩ := h.Q_de p hp
    exact ⟨P, fun t => hP (f t)⟩
  Q_ram t := h.Q_ram (f t)
  chi := h.chi
  xiR t := h.xiR (f t)
  βY := h.βY
  βX := h.βX
  βV := h.βV
  βW := h.βW

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

def RealDat.comap {A : FamIn D.what₂.LL G Pl0 T' D.R.m} (R : RealDat D A Ks) (f : T → T') (t0 : T)
    (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (FW : type_of% R.FW) (kap : ℝ)
    (lam : Fin D.R.m → T → (A.comap f t0).fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (err0 : type_of% R.err0) :
    RealDat D (A.comap f t0) Ks where
  toLevCh := R.toLevCh.comap f
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
  B := R.B.comap f t0
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
  FW := FW
  mu := mu
  twPl := twPl
  kap := kap
  lam := lam
  err0 := err0

def RealDat3.comap {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} (R : RealDat3 D A3 Ks) (f : T → T') (t0 : T)
    (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (FW : type_of% R.FW) (kap : ℝ)
    (lam : Fin D.R.m → T → (A3.comap f t0).A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (err0 : type_of% R.err0)
    (phs : Fin D.R.m → ℂ) (lam3 : Fin D.R.m → T → (A3.comap f t0).fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ) :
    RealDat3 D (A3.comap f t0) Ks where
  toRealDat := R.toRealDat.comap f t0 mu twPl FW kap lam err0
  plI := R.plI
  SF := R.SF
  phs := phs
  lam3 := lam3

def Face3.comapLv {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} (F : Face3 D A3) (f : T → T') (t0 : T) :
    Face3 D (A3.comap f t0) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

structure RealDat3.ReducedWeakCharacterisation {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  base : R.toRealDat.BaseW F.lv2
  inert : R.IsInert
  fullY : R.full_Y
  fullX : R.full_X
  fullP : R.full_P
  allPl : R.AllPlaces

theorem RealDat3.reduced_weak_of_weak_characterisation {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (h : R.WeakCharacterisation F) : R.ReducedWeakCharacterisation F :=
  ⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, h.allPl⟩

structure RealDat.ExLift {A : FamIn D.what₂.LL G Pl0 T' D.R.m} (R : RealDat D A Ks) (f : T → T') : Prop where
  ItY : ∀ k, k + 1 < D.R.m → (∃ y, ∀ t : T, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY (f t) k) (R.ptY (f t) k) y) → ∃ y, R.PItY k y
  ItX : (∃ y, ∀ t : T, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX (f t)) (R.ptX (f t)) y) → ∃ y, R.PItX y
  ioP : ∀ i, (∃ y, ∀ t : T, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i (f t)) (R.ptP i (f t)) (RealDat.Delta (D := D) i) y) →
    ∃ y, R.PIoP i y

theorem RealDat.exLift_of_ex {A : FamIn D.what₂.LL G Pl0 T' D.R.m} {R : RealDat D A Ks} (f : T → T') (h1 : R.ex_ItY) (h2 : R.ex_ItX)
    (h3 : R.ex_ioP) : R.ExLift f :=
  ⟨fun k hk _ => h1 k hk, fun _ => h2, fun i _ => h3 i⟩

theorem RealDat.exLift_of_surj {A : FamIn D.what₂.LL G Pl0 T' D.R.m} {R : RealDat D A Ks} {f : T → T'} (hs : Function.Surjective f) :
    R.ExLift f := by
  refine ⟨fun k hk ⟨y, hy⟩ => ⟨y, fun t => ?_⟩, fun ⟨y, hy⟩ => ⟨y, fun t => ?_⟩, fun i ⟨y, hy⟩ => ⟨y, fun t => ?_⟩⟩
  · obtain ⟨s, rfl⟩ := hs t; exact hy s
  · obtain ⟨s, rfl⟩ := hs t; exact hy s
  · obtain ⟨s, rfl⟩ := hs t; exact hy s

set_option maxHeartbeats 2000000 in

theorem RealDat3.reduced_weak_characterisation_comap {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (h : R.ReducedWeakCharacterisation F) {f : T → T'} (hf : Function.Injective f) {t0 : T} (h0 : f t0 = A3.A.μ0) (hex : R.toRealDat.ExLift f)
    (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T)
    (lam : Fin D.R.m → T → (A3.comap f t0).A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (phs : Fin D.R.m → ℂ)
    (lam3 : Fin D.R.m → T → (A3.comap f t0).fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ) :
    (R.comap f t0 mu R.twPl R.FW R.kap lam R.err0 phs lam3).ReducedWeakCharacterisation (F.comapLv f t0) := by
  obtain ⟨⟨hlev, hgrp, hfam, hmod, hch, hth⟩, hin, hY, hX, hP, hall⟩ := h
  refine ⟨⟨LevCh.comap_is hlev hf h0, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun t k hk => hY (f t) k hk, fun t => hX (f t),
    fun i t => hP i (f t), hall⟩
  · exact ⟨fun t q => hgrp.red_R (f t) q, fun i t q => hgrp.red_L i (f t) q, hgrp.levels, hgrp.record, hgrp.chiW⟩
  · obtain ⟨g, c0R, c0L, ht⟩ := hfam.tie
    exact ⟨⟨g, c0R, c0L, ht.comap f t0⟩, hfam.Sb, fun t PP => hfam.roots (f t) PP, hfam.pl_onto,
      fun t P => hfam.degR (f t) P, fun i t P => hfam.degL i (f t) P, fun i t P hP => hfam.muVal i (f t) P hP,
      fun P hP => hfam.etaVal P (by
        have hP' : P ∈ A3.A.ok (f t0) := hP
        rwa [h0] at hP')⟩
  · exact ⟨hmod.inf, hmod.vpos, hmod.cX, hmod.cV, hmod.prX, fun t => hmod.HX (f t), fun i t => hmod.HV i (f t), hmod.HE, hmod.HW,
      hmod.gE, hmod.gW, fun t x => hmod.jX (f t) x, fun i t x => hmod.jV i (f t) x, fun t j h2 => hmod.νY (f t) j h2,
      fun t => hmod.νY' (f t), hmod.ν0, fun t => hmod.νX (f t), fun i t => hmod.νV i (f t), hmod.νW, hmod.BV, hmod.order⟩
  · refine ⟨fun t k hk => hch.ωY (f t) k hk, fun t => hch.ωX (f t), fun t k hk => hch.vY (f t) k hk, fun t => hch.vX (f t),
      fun t k hk P => hch.ptY (f t) k hk P, fun t P => hch.ptX (f t) P, fun k hk => ?_, ?_, fun t k hk => hch.ioY (f t) k hk,
      fun t => hch.ioX (f t), fun t => hch.Th (f t)⟩
    · exact ⟨fun ⟨y, hy⟩ t => (hch.ItY k hk).1 (hex.ItY k hk ⟨y, hy⟩) (f t),
        fun hn => (hch.ItY k hk).2 fun ⟨y, hy⟩ => hn ⟨y, fun t => hy (f t)⟩⟩
    · exact ⟨fun ⟨y, hy⟩ t => hch.ItX.1 (hex.ItX ⟨y, hy⟩) (f t), fun hn => hch.ItX.2 fun ⟨y, hy⟩ => hn ⟨y, fun t => hy (f t)⟩⟩
  · refine ⟨fun i t => hth.ωP i (f t), fun i t => hth.vP i (f t), fun i t P => hth.pt_theta i (f t) P, fun i => ?_,
      fun i t => hth.thF i (f t), fun i t => hth.thG i (f t)⟩
    exact ⟨fun ⟨y, hy⟩ t => (hth.ioP i).1 (hex.ioP i ⟨y, hy⟩) (f t),
      fun hn => (hth.ioP i).2 fun ⟨y, hy⟩ => hn ⟨y, fun t => hy (f t)⟩⟩
  · exact ⟨⟨hin.tie.plI_inj, fun t Q => hin.tie.okI (f t) Q⟩, hin.onto, fun t => hin.hR (f t), fun i t => hin.hL i (f t), hin.SF⟩

end Comap

end Formalism.IndefR.Links

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section ColComap

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def tupFIncl {TU TU' : Finset (Tup X.F X.E X.K S)} (hs : TU ⊆ TU') (τ : TupF TU) : TupF TU' :=
  ⟨τ.1, τ.2.imp id fun h => hs h⟩

theorem tupFIncl_injective {TU TU' : Finset (Tup X.F X.E X.K S)} (hs : TU ⊆ TU') : Function.Injective (tupFIncl hs) := by
  intro a b h
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have h1 : a = b := congrArg Subtype.val h
  subst h1
  rfl

theorem tupFIncl_mu0F {TU TU' : Finset (Tup X.F X.E X.K S)} (hs : TU ⊆ TU') : tupFIncl hs (mu0F TU) = mu0F TU' := rfl

end ColComap

end Formalism.L2.DIV

end

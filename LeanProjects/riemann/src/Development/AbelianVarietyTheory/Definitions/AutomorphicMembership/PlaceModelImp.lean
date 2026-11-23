import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem

abbrev Late (B : Base) (C : Cols B) : Type _ := Col2.TC.Later B C

abbrev Late.st {B : Base} {C : Cols B} (a : Late B C) : Stages := ⟨B, C, a.W, a.V, a.S, a.N, a.G⟩

abbrev Late.D {B : Base} {C : Cols B} (a : Late B C) : D7 := a.st.toD7

abbrev Stages.toLate (X : Stages) : Late X.B X.C := ⟨X.W, X.V, X.S, X.N, X.G⟩

theorem Stages.late_st (X : Stages) : X.toLate.st = X := rfl

namespace R3.Tr

scoped macro:max "kc% " e:term:max : term => `((by kexactB $e))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

theorem cd_eq (c c' : CDHaar) : c = c' := by
  have h : c.cd = c'.cd := funext fun P => funext fun Q => by
    obtain ⟨x, h0, ht, h1, h2⟩ := c.trick P Q
    exact GlobalTheory.CompactDualUnique.eq_cd c' P Q _ _ x (c.haar P Q) (c.haar _ 0) (c.prob _) h0 ht h1 h2
  cases c; cases c'; cases h; rfl

def ds {V : HSp a.D} {S : a.D.what₂.Tau → SPar} (M : DSModel V S) : @DSModel b.D ((V)) ((S)) where
  H := (M.H)
  nacg := (M.nacg)
  ips := (M.ips)
  σ := (M.σ)
  lam := (M.lam)
  ε := (M.ε)
  fr := (M.fr)
  enum := (M.enum)
  ds := (M.ds)
  fr_unit := (M.fr_unit)
  fr_gram := (M.fr_gram)

def coefA {V : HSp a.D} (c : CoefA V) : @CoefA b.D ((V)) where
  W := (c.W)
  nW := (c.nW)
  iW := (c.iW)
  fW := (c.fW)
  ρ := (c.ρ)

def chFr (c : CharFrame a.D) : CharFrame b.D where
  P := (c.P)
  W := (c.W)
  mu0 := (c.mu0)
  eta := (c.eta)
  chiPsi := (c.chiPsi)
  del := (c.del)
  del' := (c.del')
  isMu0 := (c.isMu0)
  isEta := (c.isEta)
  isChi := (c.isChi)
  isDel := (c.isDel)
  isDel' := (c.isDel')

def levCh {T : Type} (L : Links.LevCh a.D T) : Links.LevCh b.D T where
  C := chFr b L.C
  xiH := (L.xiH)
  mu0 := (L.mu0)
  eta := (L.eta)
  xi := (L.xi)
  Pg := (L.Pg)
  Q := (L.Q)
  chi := (L.chi)
  xiR := (L.xiR)
  ΛY := (L.ΛY)
  ΛX := (L.ΛX)
  ΛV := (L.ΛV)
  ΛW := (L.ΛW)
  βY := (L.βY)
  βX := (L.βX)
  βV := (L.βV)
  βW := (L.βW)

def par (Q : Par a.D) : Par b.D where
  H := (Q.H)
  l := (Q.l)
  c := (Q.c)
  Dw := (Q.Dw)
  Xo := (Q.Xo)
  eO := (Q.eO)

def core (T : Core a.D) : Core b.D where
  Q := par b T.Q
  U := (T.U)
  V := (T.V)
  dict := (T.dict)
  mu := (T.mu)
  Kf := (T.Kf)
  pb := (T.pb)

def coreJ (T : CoreJ a.D) : CoreJ b.D where
  toCore := core b T.toCore
  cE := (T.cE)
  chiW := (T.chiW)
  x₀ := (T.x₀)
  iota := (T.iota)

def wt {j : ℕ} (w : WeightFamilies.Wt a.D j) : WeightFamilies.Wt b.D j where
  aP := (w.aP)
  aM := (w.aM)
  aPlus_antitone := (w.aPlus_antitone)
  aM_anti := (w.aM_anti)
  n := (w.n)
  n_even := (w.n_even)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def fam {m : ℕ} (A : FamIn a.D.what₂.LL G Pl0 T m) : FamIn b.D.what₂.LL G Pl0 T m := (A)

def fam3 {Ty : Type} {m : ℕ} (A : FamIn3 a.D.what₂.LL G Pl0 I0 Ty T m) : FamIn3 b.D.what₂.LL G Pl0 I0 Ty T m := (A)

@[reducible] def alg {Ks : Type} [Field Ks] (i : Algebra Ks a.D.what₂.LL) : Algebra Ks b.D.what₂.LL := (i)

def famReal {m : ℕ} {A : FamIn a.D.what₂.LL G Pl0 T m} {cR cL lR lL} (x : Bridge.FamReal a.D A cR cL lR lL) :
    Bridge.FamReal b.D (fam b A) ((cR)) ((cL)) ((lR)) ((lL)) where
  R := (x.R)
  L := (x.L)
  rankR := (x.rankR)
  rankL := (x.rankL)

def famM (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) : FamIn b.D.what₂.LL G Pl0 T b.D.R.m := (A)

def famInThreeCoefficientChange (A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) : FamIn3 b.D.what₂.LL G Pl0 I0 (List ℕ) T b.D.R.m := (A)

def face {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (x : Face a.D A) : Face b.D (famM b A) where
  P0 := (x.P0)
  ψ0 := (x.ψ0)
  P1 := (x.P1)
  ψ1 := (x.ψ1)
  Dc := (x.Dc)
  Sp := (x.Sp)
  Zsc := (x.Zsc)

def face3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (x : Face3 a.D A) : Face3 b.D (famInThreeCoefficientChange b A) where
  P0 := (x.P0)
  ψ0 := (x.ψ0)
  P1 := (x.P1)
  ψ1 := (x.ψ1)
  Dc := (x.Dc)
  Sp := (x.Sp)
  Zsc := (x.Zsc)

section Leaves
set_option linter.unusedVariables false

theorem autFun_imp : ∀ V f, @IsAutFun a.D V f → @IsAutFun b.D ((V)) ((f)) := fun V f h =>
  { left := (h.left)
    level := (h.level)
    cont := (h.cont) }

variable (a) in

def autFunB : type_of% (@IsAutFun b.D) := @fun V f => @IsAutFun a.D ((V)) ((f))

variable (a) in

theorem autFun_eq : @IsAutFun b.D = @autFunB B C a b := by
  funext V f
  exact propext ⟨fun h => (autFun_imp a V f h), fun h => (@autFun_imp B C a b V f h)⟩

theorem autFunSm_imp : ∀ θ V f, @IsAutFunSm a.D θ V f → @IsAutFunSm b.D ((θ)) ((V)) ((f)) := fun θ V f h =>
  { toIsAutFun := (autFun_imp b V f h.toIsAutFun)
    smooth := (h.smooth)
    zfin := (h.zfin)
    growth := (h.growth) }

variable (a) in

def autFunSmB : type_of% (@IsAutFunSm b.D) := @fun θ V f => @IsAutFunSm a.D ((θ)) ((V)) ((f))

variable (a) in

theorem autFunSm_eq : @IsAutFunSm b.D = @autFunSmB B C a b := by
  funext θ V f
  exact propext ⟨fun h => (autFunSm_imp a θ V f h), fun h => (@autFunSm_imp B C a b θ V f h)⟩

theorem multMap_imp : ∀ V S θ M J χ f, @IsMultMap a.D V S θ M J χ f → @IsMultMap b.D ((V)) ((S)) ((θ)) ((ds b M)) ((J)) ((χ)) ((f)) := fun V S θ M J χ f h =>
  { aut := fun v => (autFunSm_imp b θ V (f v) (h.aut v))
    cusp := (h.cusp)
    lev := (h.lev)
    equiv := (h.equiv)
    cont := (h.cont) }

variable (a) in

def multMapB : type_of% (@IsMultMap b.D) := @fun V S θ M J χ f => @IsMultMap a.D ((V)) ((S)) ((θ)) ((ds a M)) ((J)) ((χ)) ((f))

variable (a) in

theorem multMap_eq : @IsMultMap b.D = @multMapB B C a b := by
  funext V S θ M J χ f
  exact propext ⟨fun h => (multMap_imp a V S θ M J χ f h), fun h => (@multMap_imp B C a b V S θ (@ds B C b a V S M) J χ f h)⟩

theorem thetaFun_imp : ∀ ψ S T f, @IsThetaFunO a.D ψ S T f → @IsThetaFunO b.D ((ψ)) ((S)) ((T)) ((f)) := fun ψ S T f h =>
  { quasi := (h.quasi)
    level := (h.level)
    cont := (h.cont)
    smooth := (h.smooth) }

variable (a) in

def thetaFunB : type_of% (@IsThetaFunO b.D) := @fun ψ S T f => @IsThetaFunO a.D ((ψ)) ((S)) ((T)) ((f))

variable (a) in

theorem thetaFun_eq : @IsThetaFunO b.D = @thetaFunB B C a b := by
  funext ψ S T f
  exact propext ⟨fun h => (thetaFun_imp a ψ S T f h), fun h => (@thetaFun_imp B C a b ψ S T f h)⟩

theorem vacuum_imp : ∀ m n x1 x2 x3 x4 x5 x6 x7, @IsVacuum a.D m n x1 x2 x3 x4 x5 x6 x7 → @IsVacuum b.D m n ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) := fun m n x1 x2 x3 x4 x5 x6 x7 h =>
  { inf := (h.inf)
    theta := (h.theta)
    lat := (h.lat)
    fock := (h.fock)
    norm := (h.norm) }

variable (a) in

def vacuumB : type_of% (@IsVacuum b.D) := @fun m n x1 x2 x3 x4 x5 x6 x7 => @IsVacuum a.D m n ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7))

variable (a) in

theorem vacuum_eq : @IsVacuum b.D = @vacuumB B C a b := by
  funext m n x1 x2 x3 x4 x5 x6 x7
  exact propext ⟨fun h => (vacuum_imp a m n x1 x2 x3 x4 x5 x6 x7 h), fun h => (@vacuum_imp B C a b m n x1 x2 x3 x4 x5 x6 x7 h)⟩

theorem placeModel_imp : ∀ m n x1 x2 x3 x4 x5 x6 x7 x8, @IsPlaceModel a.D m n x1 x2 x3 x4 x5 x6 x7 x8 → @IsPlaceModel b.D m n ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) := fun m n x1 x2 x3 x4 x5 x6 x7 x8 h =>
  { trans := (h.trans)
    modul := (h.modul)
    vac := (h.vac) }

variable (a) in

def placeModelB : type_of% (@IsPlaceModel b.D) := @fun m n x1 x2 x3 x4 x5 x6 x7 x8 => @IsPlaceModel a.D m n ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8))

variable (a) in

theorem placeModel_eq : @IsPlaceModel b.D = @placeModelB B C a b := by
  funext m n x1 x2 x3 x4 x5 x6 x7 x8
  exact propext ⟨fun h => (placeModel_imp a m n x1 x2 x3 x4 x5 x6 x7 x8 h), fun h => (@placeModel_imp B C a b m n x1 x2 x3 x4 x5 x6 x7 x8 h)⟩

theorem itW_imp : ∀ V W S S' θ M M' ω pt It, @IsItW a.D V W S S' θ M M' ω pt It → @IsItW b.D ((V)) ((W)) ((S)) ((S')) ((θ)) ((ds b M)) ((ds b M')) ((ω)) ((pt)) ((It)) := fun V W S S' θ M M' ω pt It h =>
  { ne := (h.ne)
    bdd := (h.bdd)
    eqK := (h.eqK)
    eqg := (h.eqg)
    invK := (h.invK)
    invg := (h.invg) }

variable (a) in

def itWB : type_of% (@IsItW b.D) := @fun V W S S' θ M M' ω pt It => @IsItW a.D ((V)) ((W)) ((S)) ((S')) ((θ)) ((ds a M)) ((ds a M')) ((ω)) ((pt)) ((It))

variable (a) in

theorem itW_eq : @IsItW b.D = @itWB B C a b := by
  funext V W S S' θ M M' ω pt It
  exact propext ⟨fun h => (itW_imp a V W S S' θ M M' ω pt It h), fun h => (@itW_imp B C a b V W S S' θ (@ds B C b a V S M) (@ds B C b a W S' M') ω pt It h)⟩

theorem pairSetup_imp : ∀ ψ θ S T x1 x2 x3 x4 x5 x6, @Fock.Sk.PairSetup a.D ψ θ S T x1 x2 x3 x4 x5 x6 → @Fock.Sk.PairSetup b.D ((ψ)) ((θ)) ((S)) ((T)) ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) := fun ψ θ S T x1 x2 x3 x4 x5 x6 h =>
  { std := (h.std)
    inf := (h.inf)
    cartS := (h.cartS)
    cartT := (h.cartT)
    onbS := (h.onbS)
    onbT := (h.onbT) }

variable (a) in

def pairSetupB : type_of% (@Fock.Sk.PairSetup b.D) := @fun ψ θ S T x1 x2 x3 x4 x5 x6 => @Fock.Sk.PairSetup a.D ((ψ)) ((θ)) ((S)) ((T)) ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6))

variable (a) in

theorem pairSetup_eq : @Fock.Sk.PairSetup b.D = @pairSetupB B C a b := by
  funext ψ θ S T x1 x2 x3 x4 x5 x6
  exact propext ⟨fun h => (pairSetup_imp a ψ θ S T x1 x2 x3 x4 x5 x6 h), fun h => (@pairSetup_imp B C a b ψ θ S T x1 x2 x3 x4 x5 x6 h)⟩

theorem inertTie_imp : ∀ G i1 i2 P I Ty T m A x1 x2 x3, @Bridge.InertTie a.D G i1 i2 P I Ty T m A x1 x2 x3 → @Bridge.InertTie b.D G i1 i2 P I Ty T m ((A)) ((x1)) ((x2)) ((x3)) := fun G i1 i2 P I Ty T m A x1 x2 x3 h =>
  { plI_inj := (h.plI_inj)
    okI := (h.okI) }

variable (a) in

def inertTieB : type_of% (@Bridge.InertTie b.D) := @fun G i1 i2 P I Ty T m A x1 x2 x3 => @Bridge.InertTie a.D G i1 i2 P I Ty T m ((A)) ((x1)) ((x2)) ((x3))

variable (a) in

theorem inertTie_eq : @Bridge.InertTie b.D = @inertTieB B C a b := by
  funext G i1 i2 P I Ty T m A x1 x2 x3
  exact propext ⟨fun h => (inertTie_imp a G i1 i2 P I Ty T m A x1 x2 x3 h), fun h => (@inertTie_imp B C a b G i1 i2 P I Ty T m A x1 x2 x3 h)⟩

theorem famTie_imp : ∀ G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9, @Bridge.FamTie a.D G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9 → @Bridge.FamTie b.D G i1 i2 P T m ((A)) ((cR)) ((cL)) ((lR)) ((lL)) ((@famReal B C a b G i1 i2 P T m A cR cL lR lL x)) ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9)) := fun G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9 h =>
  { ranks := (h.ranks)
    v0 := (h.v0)
    tauL_ok := (h.tauL_ok)
    pl_inj := (h.pl_inj)
    q := (h.q)
    S_fin := (h.S_fin)
    ok := (h.ok)
    gramR_eq := (h.gramR_eq)
    mapR := (h.mapR)
    mapL := (h.mapL)
    coefR := (h.coefR)
    coefL := (h.coefL) }

variable (a) in

def famTieB : type_of% (@Bridge.FamTie b.D) := @fun G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9 => @Bridge.FamTie a.D G i1 i2 P T m ((A)) ((cR)) ((cL)) ((lR)) ((lL)) ((famReal a x)) ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))

variable (a) in

theorem famTie_eq : @Bridge.FamTie b.D = @famTieB B C a b := by
  funext G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9
  exact propext ⟨fun h => (famTie_imp a G i1 i2 P T m A cR cL lR lL x x1 x2 x3 x4 x5 x6 x7 x8 x9 h), fun h => (@famTie_imp B C a b G i1 i2 P T m A cR cL lR lL (@famReal B C b a G i1 i2 P T m A cR cL lR lL x) x1 x2 x3 x4 x5 x6 x7 x8 x9 h)⟩

theorem weilDatum_imp : ∀ ψ S T x1 x2 ω, @IsWeilDatumO a.D ψ S T x1 x2 ω → @IsWeilDatumO b.D ((ψ)) ((S)) ((T)) ((x1)) ((x2)) ((ω)) := fun ψ S T x1 x2 ω h =>
  { std := (h.std)
    hecS := (h.hecS)
    hecT := (h.hecT)
    resS := (h.resS)
    resT := (h.resT)
    om_pres := by rewrite [thetaFun_eq a b]; exact (h.om_pres)
    om_heis := by rewrite [thetaFun_eq a b]; exact (h.om_heis)
    om_aut := by rewrite [thetaFun_eq a b]; exact (h.om_aut)
    om_cont := by rewrite [thetaFun_eq a b]; exact (h.om_cont)
    om_unit := by rewrite [thetaFun_eq a b]; exact (h.om_unit)
    om_split := by rewrite [thetaFun_eq a b]; exact (h.om_split) }

variable (a) in

def weilDatumB : type_of% (@IsWeilDatumO b.D) := @fun ψ S T x1 x2 ω => @IsWeilDatumO a.D ((ψ)) ((S)) ((T)) ((x1)) ((x2)) ((ω))

variable (a) in

theorem weilDatum_eq : @IsWeilDatumO b.D = @weilDatumB B C a b := by
  funext ψ S T x1 x2 ω
  exact propext ⟨fun h => (weilDatum_imp a ψ S T x1 x2 ω h), fun h => (@weilDatum_imp B C a b ψ S T x1 x2 ω h)⟩

theorem weilFull_imp : ∀ ψ S T x1 x2 ω, @WeilFull.IsWeilFull a.D ψ S T x1 x2 ω → @WeilFull.IsWeilFull b.D ((ψ)) ((S)) ((T)) ((x1)) ((x2)) ((ω)) := fun ψ S T x1 x2 ω h =>
  { datum := (weilDatum_imp b ψ S T x1 x2 ω h.datum)
    inert := by delta WeilFull.SphInertAtO; rewrite [thetaFun_eq a b]; exact (h.inert)
    real := by delta WeilFull.RealAtO; rewrite [pairSetup_eq a b]; (try rewrite [thetaFun_eq a b]); exact (h.real) }

variable (a) in

def weilFullB : type_of% (@WeilFull.IsWeilFull b.D) := @fun ψ S T x1 x2 ω => @WeilFull.IsWeilFull a.D ((ψ)) ((S)) ((T)) ((x1)) ((x2)) ((ω))

variable (a) in

theorem weilFull_eq : @WeilFull.IsWeilFull b.D = @weilFullB B C a b := by
  funext ψ S T x1 x2 ω
  exact propext ⟨fun h => (weilFull_imp a ψ S T x1 x2 ω h), fun h => (@weilFull_imp B C a b ψ S T x1 x2 ω h)⟩

variable (a) in

def multB : type_of% (@Mult.Mult b.D) := @fun V S θ M J χ => (@Mult (@Late.D B C a) V S θ (@ds B C b a V S M) J χ)

variable (a) in

theorem mult_eq : @Mult.Mult b.D = @multB B C a b := by
  funext V S θ M J χ
  delta Mult.Mult
  rewrite [multMap_eq a b]
  exact (Eq.refl (multB a b θ M J χ))

end Leaves

variable (a) in

def multTB : type_of% (@MultT b.D) := @fun V S θ M J χ => (@MultT (@Late.D B C a) V S θ (@ds B C b a V S M) J χ)

variable (a) in

theorem multT_eq : @MultT b.D = @multTB B C a b := by
  funext V S θ M J χ
  delta MultT
  rewrite [mult_eq a b]
  exact (Eq.refl (multTB a b θ M J χ))

def castAlong {α β : Type} (e : α = β) (x : α) : {y : β // HEq x y} :=
  Classical.choice ⟨⟨cast e x, (cast_heq e x).symm⟩⟩

theorem castAlong_rfl {α : Type} (x : α) : (castAlong rfl x).1 = x := (eq_of_heq (castAlong rfl x).2).symm

section LiftTypes

variable {D : D7} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IoYT (m : type_of% (@MultT D)) (R : RealDat D A Ks) : Type :=
  ∀ t k, m R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) (R.toLevCh.datYt t (k + 1) R.toLevCh.triv))
      (levChi _ (R.βY (k + 1)) (R.toLevCh.datYt t (k + 1) R.toLevCh.triv)) →ₗ[ℂ]
    m R.θ (R.MY k) (levS _ (R.βY k) (R.toLevCh.datYt t k R.toLevCh.triv)) (levChi _ (R.βY k) (R.toLevCh.datYt t k R.toLevCh.triv))

def IoXT (m : type_of% (@MultT D)) (R : RealDat D A Ks) : Type :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ]
    m R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) (R.toLevCh.datYt t (D.R.m - 1) R.toLevCh.triv))
      (levChi _ (R.βY (D.R.m - 1)) (R.toLevCh.datYt t (D.R.m - 1) R.toLevCh.triv))

end LiftTypes

variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def ioYB {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) : IoYT (@multTB B C b a) R :=
  (castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) ((R.ioY))).1

def ioXB {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) : IoXT (@multTB B C b a) R :=
  (castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) ((R.ioX))).1

end R3.Tr

end GlobalTheory.Mem

end

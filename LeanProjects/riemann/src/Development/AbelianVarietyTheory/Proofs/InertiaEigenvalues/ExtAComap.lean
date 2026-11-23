import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type}

def extL (L : LevCh D T) (s : N → T) (a : N → ℕ) : LevCh D (T ⊕ N) :=
  { L with
    xiH := Sum.elim L.xiH fun n => L.xiH (s n) ^ a n
    xi := Sum.elim L.xi fun n => L.xi (s n) ^ a n
    Q := Sum.elim L.Q fun n => L.Q (s n)
    xiR := Sum.elim L.xiR fun n PP => L.xiR (s n) PP ^ a n }

structure NewFam {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (s : N → T) where
  muVal : Fin m → N → Pl0 → Kˣ
  SR : N → CSD K
  actR : ∀ n, Representation K G (SR n).Forms
  opR : ∀ n, A.ok (s n) × ℕ → Module.End K (SR n).Forms
  SL : Fin m → N → CSD K
  actL : ∀ j n, Representation K G (SL j n).Forms
  opL : ∀ j n, A.ok (s n) × ℕ → Module.End K (SL j n).Forms

def extA {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) {s : N → T} (X : NewFam A s) :
    FamIn K G Pl0 (T ⊕ N) m where
  v0 := A.v0
  μ0 := .inl A.μ0
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j := Sum.elim (A.muVal j) (X.muVal j)
  etaVal := A.etaVal
  ok := Sum.elim A.ok fun n => A.ok (s n)
  MtildeCSD := Sum.elim A.MtildeCSD X.SR
  leftGroupActionRight τ := Sum.rec A.leftGroupActionRight X.actR τ
  heckeR τ := Sum.rec A.heckeR X.opR τ
  MtCSD j := Sum.elim (A.MtCSD j) (X.SL j)
  leftGroupActionLift j τ := Sum.rec (A.leftGroupActionLift j) (X.actL j) τ
  heckeL j τ := Sum.rec (A.heckeL j) (X.opL j) τ

theorem extA_comap {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) {s : N → T}
    (X : NewFam A s) : (extA A X).comap Sum.inl A.μ0 = A := rfl

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure NewReal (R : RealDat D A Ks) {s : N → T} (a : N → ℕ) (X : NewFam A s) where
  BR : ∀ n, Bridge.SideReal D D.sp.X'
    (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh s a).datXt (.inr n)) R.pl (A.ok (s n))))
    (X.SR n) (X.actR n) (X.opR n) (fun i => i.2)
  BL : ∀ i n, Bridge.SideReal D (Vc D i)
    (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh s a).datVt i (.inr n)) R.pl (A.ok (s n))))
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
  ioY : ∀ n k, MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv))
      (Lev.levChi _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv)) →ₗ[ℂ]
    MultT R.θ (R.MY k) (levS _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
      (Lev.levChi _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
  ioX : ∀ n, LinearMap.range (R.cX.toMap R.prX ∘ₗ (HX n).e) →ₗ[ℂ]
    MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
      (Lev.levChi _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
  Th : ∀ n, (HX n).H →ₗ[ℂ] R.HE.H
  thF : ∀ i n, (HV i n).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))
  thG : ∀ i n, (HV i n).H →ₗ[ℂ] (R.HW i (sg0 D A)).H

set_option maxHeartbeats 4000000 in

def extR (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) : RealDat D (extA A X) Ks where
  toLevCh := extL R.toLevCh s a
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
theorem extR_comap (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) :
    (extR R Y).comap Sum.inl A.μ0 R.mu R.twPl R.FW R.kap R.lam R.err0 = R := rfl

end GlobalTheory.ConjExt

end

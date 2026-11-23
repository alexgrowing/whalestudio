import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

structure PC where
  CkLow : ℝ
  Ck6 : ℝ
  CfL : ℝ
  cLL : ℝ
  CnW : ℝ
  Crho : ℝ
  CDelG : ℝ
  CLw : ℝ
  Cj0 : ℝ
  Cw : ℝ
  cw : ℝ
  CDel : ℝ
  CCount : ℝ
  Ch0r : ℝ
  Ch0k : ℝ
  Ch0N : ℝ
  Cgap : ℝ
  CetaF : ℝ
  CY : ℝ
  CYL : ℝ
  Cpde : ℝ
  CccK : ℝ
  CF : ℝ

def PC.list (P : PC) : List ℝ :=
  [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
    P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
    P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF]

structure PTC where
  CP : ℝ
  eP : ℝ
  Cp : ℝ
  Cb : ℝ
  cTO : ℝ
  ChT : ℝ
  CbN : ℝ

def PTC.list (P : PTC) : List ℝ := [P.CP, P.eP, P.Cp, P.Cb, P.cTO, P.ChT, P.CbN]

structure FC where
  Ct : ℝ
  Cc : ℝ
  CT2 : ℝ
  CGam : ℝ
  Csz : ℝ
  Cr : ℝ
  CTu : ℝ

  Cdg : ℝ

  C5 : ℝ

  full : Prop
  GK : G.Consts
  cX : ExtraC
  P : PC
  T : PTC

def FC.PK (C : FC) : List ℝ := C.P.list

def FC.PT (C : FC) : List ℝ := C.T.list

def FC.cPre (C : FC) : List ℝ := [C.T.CP]

def FC.cOut (C : FC) : List ℝ := [C.Ct, C.Cc, C.CT2, C.P.CLw, C.P.Cj0, C.P.cw, C.P.CYL, C.P.Cpde, C.P.CccK,
  C.T.CP, C.T.Cp, C.T.eP, C.T.cTO, C.CTu, C.P.CetaF, C.P.Cpde]

def FC.cMid (C : FC) (CH : ℝ) : List ℝ := [CH, C.CGam, C.Csz, C.Csz, C.Csz, C.Csz, C.Csz,
  C.cX.err.g, C.GK.La, C.P.CF]

def FC.cLast (C : FC) : List ℝ := [C.P.CkLow, C.P.Ck6, C.P.CfL, C.P.cLL⁻¹, C.P.Crho, C.P.Crho, C.P.CDelG, C.P.Cw,
  C.P.CDel, C.P.CCount, C.P.Ch0r, C.P.Ch0k, C.P.Ch0N, C.P.Cgap, C.P.CY, C.T.Cb, C.T.ChT, C.T.CbN,
  C.GK.rho, C.GK.kII, C.GK.tII, C.GK.DII, C.GK.szII, C.GK.kII', C.GK.DI, C.GK.kappaThresholdOne,
  C.GK.kappaThresholdTwo, C.GK.kI, C.GK.CN, C.GK.CN, C.GK.CN, C.GK.CN]

def FC.Fixed (C : FC) : Prop :=
  C.GK.Pr1 = 1 ∧ C.GK.dl1 = 5 ∧ C.GK.dl2 = 4 ∧ C.cX.Ce = 1 ∧ C.cX.err.c6 = 12 ∧ C.cX.err.dig = 3 ∧ C.Cr = 1 ∧
    C.P.CnW = 10 ∧ 12 ≤ C.T.eP ∧ C.Ct = 401

def FC.Large (C : FC) (K : TransportedAlt) (CH : ℝ) : Prop :=
  (∀ c ∈ C.cPre, K.pre ≤ c) ∧ True ∧ (∀ c ∈ C.cMid CH, K.mid C.cOut ≤ c) ∧
    ∀ c ∈ C.cLast, K.last (C.cOut ++ C.cMid CH) ≤ c

structure Out where
  Cc : ℝ
  CT2 : ℝ
  CLw : ℝ
  Cj0 : ℝ
  cw : ℝ
  CYL : ℝ
  Cpde : ℝ
  CccK : ℝ
  Cp : ℝ
  eP : ℝ
  cTO : ℝ
  CTu : ℝ
  CetaF : ℝ
  Cdg : ℝ
  C5 : ℝ
  full : Prop

def FC.out (C : FC) : Out :=
  ⟨C.Cc, C.CT2, C.P.CLw, C.P.Cj0, C.P.cw, C.P.CYL, C.P.Cpde, C.P.CccK, C.T.Cp, C.T.eP, C.T.cTO, C.CTu, C.P.CetaF, C.Cdg,
    C.C5, C.full⟩

def bTopOf {D : D7} (L : SizeData₂ D) : ℝ :=
  L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ)

structure NumAt (C : FC) {D : D7} (L : SizeData₂ D) where
  params : ParameterChoice' D L
  params_K : parConsts params = C.PK
  CnW_eq : params.CnW = C.P.CnW
  parT : ParamsT D L params
  parT_K : [parT.CP, parT.eP, parT.Cp, parT.Cb, parT.cTO, parT.ChT, parT.CbN] = C.PT
  eP_eq : parT.eP = C.T.eP
  sizes : SizesAt L
  rho_le : G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ)
  CGam_eq : L.CGam = C.CGam
  Cc_eq : L.Cc = C.Cc
  Ct_eq : L.Ct = C.Ct
  secondConstant_eq : D.host.CT2 = C.CT2
  LaG_ge : L.sc.x ^ L.sc.eps ≤ L.LaG
  bT_le : ∀ t, (L.bT t : ℝ) ≤ bTopOf L

  ccK_top : D.host.ccK = ⊤
  g_le : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)
  pde_lt : (D.host.pde : ℝ) < L.sc.X' ∧ (D.host.pde' : ℝ) < L.sc.X'
  logFiveDepth_eq : L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
  Lw_eq : D.host.Lw = 10 * ⌈(C.Ct + 4) * Real.log L.sc.x⌉₊ + 2 * ⌈30 / L.sc.eps⌉₊ + 22
  cloud1 : ∀ τ τ', (D.hc τ).v = (D.hc τ').v
  win : (L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps)) ∧
    (Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ 2 * Real.sqrt (L.sc.x * L.sc.delta1)) ∧
    (L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps))

structure TiesAt (C : FC) {D : D7} (L : SizeData₂ D) (gatT : GatTies D) where
  Gx : G.Inst D L
  Gy : G.LatInst D
  supp_sat : ∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp
  tw_supp : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp
  fills : ∀ w, G.ParametersFill Gx C.GK w
  lats0 : ∀ w u, G.VV Gx C.GK (G.aL L) (G.bL L) (D.what₂.places.resChar w) = ∅ →
    D.what₂.places.resChar w ≠ (D.mem u).A.T → L.lenMN u w = 0
  latTied : G.LatTied gatT Gx Gy
  drop_iff : ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain Gx C.GK C.Cr p ∧ ∀ u, p ≠ (D.mem u).A.T)

structure ExtraAt (C : FC) {D : D7} (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) where
  ties : Ties D
  X : DivX D
  nuDef : DV.NuDef D L
  nprimeDef : DV.NprimeDef D L
  rrDef : DV.RRDef D
  h_eq : ∀ u, D.div.h u = DV.hExpl6 D L X C.Csz u
  ex : Extra D L gatT Gx Gy C.GK X C.cX

def QDq (x eps C : ℝ) (q d : ℕ) : Prop :=
  BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧
  BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d)

def Boxq (x eps : ℝ) (q d : ℕ) : Prop :=
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (GlobalTheoryTheory.chDir d) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir d a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps)
    (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d)

def Rowq (x eps : ℝ) (n q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧
  GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧
  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

structure MoreH (sc : Scale) (C : FC) (Y : Σ R : Ranks, Host R) : Prop where
  t2 : Y.2.secondSet_card_lower_bound
  tt : sc.delta1 * Y.1.n / 2 ≤ (Y.2.TT.card : ℝ) ∧ (Y.2.TT.card : ℝ) ≤ 2 * sc.delta1 * Y.1.n
  qd : C.full → QDq sc.x sc.eps C.C5 Y.2.q Y.2.d
  boxes : C.full → Boxq sc.x sc.eps Y.2.q Y.2.d
  what₂ : C.full → Rowq sc.x sc.eps Y.1.n Y.2.q Y.2.d

@[ext] structure Shd where
  R : Ranks
  TTn : Finset ℕ
  T2 : Finset ℕ
  q : ℕ
  d : ℕ
  g : Fin 2 → ℕ
  pde : ℕ
  pde' : ℕ
  bits : ℕ → Bool
  LaG : ℝ
  etaSz : ℝ
  Sc : ℝ
  hP : ℕ → ℕ
  bs : ℕ → ℕ → ℕ
  off : ℕ → ℕ → ℝ
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

def Win (sc : Scale) (k : ℕ) (TTn : Finset ℕ) (bTop : ℝ) (a b : ℕ → ℤ) : Prop :=
  ∀ t ∈ TTn, (sc.a ≤ (a t : ℝ) ∧ (a t : ℝ) ≤ sc.a + sc.a / ((k : ℝ) * sc.x ^ (Scale.A / 2))) ∧
    sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTop

def Shd.bTop (S : Shd) (sc : Scale) : ℝ :=
  sc.b' + 2 * (S.R.n : ℝ) * sc.delta1 * sc.x ^ sc.eps * S.LaG * sc.b' / (S.R.k : ℝ)

end Formalism.MainNotions.Inhab

end

import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Rec
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.Divisibility.RecBridgeMkF
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Cp

open Formalism Formalism.L2 Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

abbrev fieldsLL (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) : Formalism.L2.Col.Fields :=
  { X with K := D.what₂.LL, fieldK := inferInstance, nfK := inferInstance, starK := inferInstance, emb := e }

section ColRec

open Formalism.BasicNotions Formalism.L2.Col

structure ColRec3 (X : Fields) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
    (A3 : FamIn3 X.K G Pl0 I0 Ty T m) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) where
  Pr : Primes X
  Rk : Ranks
  W : Wts X Pr.Word Rk
  Ch : Chars X Pr Rk.m
  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  Sg : Set ℕ
  hX : X.Ok
  Lv : LevFam X.E X.K Rk.r Pr.vGs
  Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs Rk.r → X.K)
  m2 : ℕ
  Gc : ChGlob X Rk.m
  mu : A3.fam3.base3.Tup → Tup X.F X.E X.K Sg
  cst : ∀ t, LocCst X (rowSG Pr sel (mu t))
  Li : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))
  hL : ∀ t, (Li t).Ok Ch sel (mu t) (cst t) Gc m2
  hP : ∀ t, (mtildeGSD W Ch sel (mu t) Lv).Ok
  Mem : Type
  wd : Mem → Pr.Word
  b : ∀ t, Mem → (Li t).β (m2 + 1)
  hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (Li t) (wd x) m2 (b t x)
  Am : Formalism.L2.Ker.Amb X
  hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (Li t) Am (wd x) m2 (b t x) (hY t x) Lv
  hF : ∀ t x j, (chF W sel (mu t) (Li t) (wd x) j).Ok
  hE : ∀ x, (evGSD W Ch sel (mu A3.fam3.base3.μ0) Lv (wd x)).Ok
  ev : ∀ (Zs : DefSub A3.fam3.amb3) t, (Fin ((A3.side3 P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg Lv

variable {X : Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}

abbrev ColRec3.ker (c : ColRec3 X A3 P1 ψ1) :
    ∀ t x, ChKer c.W c.Ch c.sel (c.mu t) (c.cst t) (c.Li t) c.Lv (c.wd x) c.m2 (c.b t x) (c.hY t x) :=
  kerRec c.mu c.cst c.Li c.wd c.b c.hY c.Am c.hK

abbrev ColRec3.face (c : ColRec3 X A3 P1 ψ1) (Zs : DefSub A3.fam3.amb3) : DefCols (A3.side3 P1 ψ1 Zs) :=
  colFace c.hX (A3.side3 P1 ψ1 Zs) c.Xg c.mu c.cst c.Li c.hL c.hP c.Mem c.wd c.b c.hY c.ker c.hF (c.ev Zs)

abbrev ColRec3.memQ (c : ColRec3 X A3 P1 ψ1) (x : c.Mem) : KerChain X.K :=
  Formalism.L2.DIV.memQ (A := c.ker) (hF := c.hF) c.hE (x := x)

end ColRec

section IndefiniteRowSideFullHecke

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def ColTie3 (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)) : Prop :=
  c.face P.Zs = P.Dc ∧ HEq (Sp P.Zs) P.Sp

def ColTieT (T : TiedDataSK ex) (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) : Prop :=
  T.ker.X = fieldsLL D X e ∧ c.Rk = D.R ∧ HEq c.Pr T.ker.Pr ∧ HEq c.Ch T.ker.Ch ∧ HEq c.sel T.ker.sel ∧ HEq c.Sg T.ker.S ∧
    HEq c.mu (fun t => T.ker.tup (P.I.tup t)) ∧ HEq c.cst (fun t => T.ker.cst (P.I.tup t)) ∧
    HEq c.Li (fun t => T.ker.idx (P.I.tup t)) ∧ c.m2 = T.ker.m2 ∧ HEq c.Gc T.ker.glob ∧
    HEq c.Am (Formalism.L2.Ker.ambOf T.ker.seam T.ker.B T.ker.χ T.ker.cD) ∧ c.Mem = D.what₂.Word ∧ HEq c.wd T.ker.word

structure SquareIntegrableColumnsCompatible (T : TiedDataSK ex) (P : RowSideFamily ex) : Type 1 where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  colTie : ColTie3 P X e c Sp
  kerTie : ColTieT T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1

end IndefiniteRowSideFullHecke

end GlobalTheory.Cp

end

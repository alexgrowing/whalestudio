import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinD
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.L2.DIV Formalism.L2.Indef

section Joint

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 I0 Ty T : Type}
  (A3 : FamIn3 D.what₂.LL Gp Pl0 I0 Ty T D.R.m)

structure BaseDivisionAmbientCompatibilityFamily (Y : DivX D) (p0 : BaseLevelRowSide D) (a0 : AmbForm D p0.s)
    (P0 : Subgroup Gp) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup Gp) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 p0 Dc)
    (JA : AmbIds D A3.A p0.s a0 P0 ψ0 I.tup) (JM : MjHIds D A3.A Y (A3.indefDown S0)) : Prop where

  div : DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 p0 C NuC I

  amb0 : AmbTie D A3.A p0.s a0 P0 ψ0 I.tup I.jA0 JA

  mjH : MjHTie D A3.A Y (A3.indefDown S0) I.jW JM

  cen0 : CenTie D A3.A p0.s P0 ψ0 I.eG I.tup I.jA0

end Joint

section Bundle

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure RowSideFamily (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where
  Gp : Type
  [grp : Group Gp]
  [fin : Fintype Gp]
  Pl0 : Type
  I0 : Type
  T : Type

  A3 : FamIn3 D.what₂.LL Gp Pl0 I0 (List ℕ) T D.R.m
  P0 : Subgroup Gp
  ψ0 : P0 →* D.what₂.LLˣ
  Ps : Subgroup Gp
  ψs : Ps →* D.what₂.LLˣ
  Zs : DefSub A3.fam3.amb3
  S0 : IndefData (A3.side3 P0 ψ0 Zs)
  S1 : IndefData (A3.side3 Ps ψs Zs)
  Dc : DefCols (A3.side3 Ps ψs Zs)
  Sp : SPer Dc
  C : ColData Dc Sp S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)
  I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 ex.p0 Dc
  JA : AmbIds D A3.A ex.p0.s ex.amb0 P0 ψ0 I.tup
  JM : MjHIds D A3.A Y (A3.indefDown S0)
  tied : BaseDivisionAmbientCompatibilityFamily D A3 Y ex.p0 ex.amb0 P0 ψ0 Ps ψs Zs S0 S1 C NuC I JA JM

attribute [instance] RowSideFamily.grp RowSideFamily.fin

variable {ex : Extra D L hT Gi Gl Kc Y cX}

def cjS (b : Bool) : ℂ →+* ℂ := Formalism.IndefR.Links.cj b

def twS (P : RowSideFamily ex) : Bool := Formalism.IndefR.Links.twAt D.what₂.embLL P.A3.fam3.base3.v0

open Classical in

structure RowSideDetermined (T : TiedDataSK ex) (P : RowSideFamily ex) : Prop where

  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)

  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), LowerMapTieTw T u μ hμ h1

  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂

  ambS : ∃ JA : AmbIds D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup,
    AmbTie D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup P.I.jA JA

  faces : ∃ (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf P.Zs = P.Dc ∧ HEq (Spf P.Zs) P.Sp

  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam

noncomputable def RowSideDetermined.columnsOfSubspaces {T : TiedDataSK ex} {P : RowSideFamily ex} (h : RowSideDetermined T P) :
    ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs) :=
  Classical.choose h.faces

noncomputable def RowSideDetermined.periodOfSubspaces {T : TiedDataSK ex} {P : RowSideFamily ex} (h : RowSideDetermined T P) : ∀ Zs, SPer (h.columnsOfSubspaces Zs) :=
  Classical.choose (Classical.choose_spec h.faces)

theorem RowSideDetermined.columns_function_at_subspaces {T : TiedDataSK ex} {P : RowSideFamily ex} (h : RowSideDetermined T P) : h.columnsOfSubspaces P.Zs = P.Dc :=
  (Classical.choose_spec (Classical.choose_spec h.faces)).1

theorem RowSideDetermined.period_function_at_subspaces {T : TiedDataSK ex} {P : RowSideFamily ex} (h : RowSideDetermined T P) : HEq (h.periodOfSubspaces P.Zs) P.Sp :=
  (Classical.choose_spec (Classical.choose_spec h.faces)).2

structure RowsHold0_3 (P : RowSideFamily ex) : Prop where
  zsSt : P.Zs.Stable
  zsBl : P.Zs.InBlock
  rows0 : ∃ R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 P.Zs), R0.toIndefData = P.S0
  famOk : ∃ s, P.A3.fam3.Ok3 s
  famSep : P.A3.fam3.TypesSep3

structure RowsHold3 (P : RowSideFamily ex) : Prop extends RowsHold0_3 P where
  lvl : LevelLink P.S0 P.S1
  buRat : D.BuRational
  pkg : ∃ (N : IndefNum P.A3.fam3.base3) (Sc : IndefColsR (P.A3.side3 P.Ps P.ψs P.Zs) P.Dc P.Sp N),
    Sc.toIndefData = P.S1 ∧ HEq Sc.col P.C

def RowsHoldPer3 (T : TiedDataSK ex) : Prop := Formalism.L2.GlobalTheoryTheory.PerDec.PeriodDecompositionBase T

def RowsHoldKap3 (P : RowSideFamily ex) : Prop := ∀ e : D.what₂.LL →+* ℂ, Y.kapR e = P.S1.κ (InfinitePlace.mk e)

def RowsHoldDrows3 (P : RowSideFamily ex) : Prop := D.what₂.Drows = P.S1.D

open Classical in

def RowsHoldLam3 (P : RowSideFamily ex) : Prop :=
  ∃ cOf : D.what₂.FT → P.A3.fam3.base3.Ix,
    (∀ (i : Fin D.R.m) (c : P.A3.fam3.base3.Ix),
      iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) ∧
      (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
        Submodule.span ℂ ((P.I.jW i) '' (P.S0.Wp i c : Set (Fin (P.S0.dW i) → D.what₂.LL)))) ∧
    (∀ (i : Fin D.R.m) (t : P.T) (σ : D.what₂.FT),
      (P.I.tup t = D.what₂.mu0 ∨ ∃ w, P.I.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
      D.what₂.lamP (P.I.tup t) ((i : ℕ) + 1) σ = P.S0.lam i t (cOf σ) P.A3.fam3.base3.v0) ∧
    (∀ c : P.A3.fam3.base3.Ix,
      ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = Module.finrank D.what₂.LL (P.S0.Ep c))

def RowsHoldDcPt3 (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T) (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL)
    (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

def IsBCLL0 {d : ℕ} (Λ : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL)) : Prop :=
  ∃ B : Submodule (𝓞 ↥D.LL0) (Fin d → ↥D.LL0),
    Λ = Submodule.span (𝓞 D.what₂.LL) ((fun v i => ((v i : ↥D.LL0) : D.what₂.LL)) '' (B : Set (Fin d → ↥D.LL0)))

def RowsHoldBC3 (P : RowSideFamily ex) : Prop :=
  IsBCLL0 ((P.A3.side3 P.P0 P.ψ0 P.Zs).abelian₂ P.A3.fam3.base3.μ0) ∧ ∀ i, IsBCLL0 (P.S0.M i)

def RowsHoldPerTw3 (T : TiedDataSK ex) : Prop := Formalism.L2.GlobalTheoryTheory.PerDec.PeriodDecompositionTwisted T

def RowsHoldPtTw3 (T : TiedDataSK ex) : Prop := Formalism.L2.GlobalTheoryTheory.PerDec.LowerTwistedAtTuples T

def LowerMapPeriod : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} (T : TiedDataSK ex) (P : RowSideFamily ex), RowSideDetermined T P → RowsHold3 P →
    ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
      D.what₂.embLL (D.div.Bk u φ x) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) (D.what₂.sec D.what₂.mu0 (D.jEE x))

def PairingPeriod : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} (T : TiedDataSK ex) (P : RowSideFamily ex), RowSideDetermined T P → RowsHold3 P →
    Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I →
    ∀ u (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (y : Fin P.S1.D → D.what₂.LL),
      D.what₂.embLL (P.C.B (P.I.wU u) x y) =
        D.what₂.perCol u D.what₂.mu0 (D.jN u (P.I.eNu u x)) (D.what₂.sec D.what₂.mu0 (D.jEE (P.I.eRR y)))

end Bundle

end Formalism.L2.Rows

end

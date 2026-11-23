import Formalism.LocalToGlobal.ClassSK
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalToGlobal.HermitianForms.TiedBr

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def LowerMapTieS {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u Tf.til.z0) P
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

def LowerMapTieTw {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u (T.tw.pt.til u μ hμ h1).z0).det → ∀ (ψ : (D.PTw u μ).Wz) (c : (ex.tw.fm u μ).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, T.tw.ptE.eWz u μ ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u (T.tw.pt.til u μ hμ h1).z0) P
        (Formalism.L2.Forms.twYS T.tw.ch T.cols.forms u μ D.R.m le_rfl s)) →
    (T.tw.pt.val u μ hμ).eW ((D.PTw u μ).lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

open Classical in

structure RowPinS (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex) : Prop where

  ftTie : ∃ cOf : D.what₂.FT → Q.A.fam.base.Ix,
    (∀ (i : Fin D.R.m) (c : Q.A.fam.base.Ix),
      iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) ∧
      (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
        Submodule.span ℂ ((Q.I.jW i) '' (Q.S0.Wp i c : Set (Fin (Q.S0.dW i) → D.what₂.LL)))) ∧
    (∀ c : Q.A.fam.base.Ix,
      ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = Module.finrank D.what₂.LL (Q.S0.Ep c))

  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)

  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m), LowerMapTieTw T u μ hμ h1

  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂

  dcPt : ∀ (u : D.what₂.Word) (t : Q.T) (x : Fin (Q.Dc.a (Q.I.wU u)) → D.what₂.LL)
    (F : Fin ((Q.A.side Q.Ps Q.ψs Q.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (Q.Dc.Pt (Q.I.wU u) t x F) =
      D.what₂.perCol u (Q.I.tup t) (D.jN u (Q.I.eNu u x)) (Q.I.jA t ((rV0 D Q.A Q.Ps Q.ψs t).mulVec F))

  drows : D.what₂.Drows = Q.S1.D

  kap : ∀ e : D.what₂.LL →+* ℂ, Y.kapR e = Q.S1.κ (InfinitePlace.mk e)

  ambS : ∃ JA : AmbIds D Q.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb Q.Ps Q.ψs Q.I.tup,
    AmbTie D Q.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb Q.Ps Q.ψs Q.I.tup Q.I.jA JA

  faces : ∃ (Dcf : ∀ Zs : DefSub Q.A.fam.amb, DefCols (Q.A.side Q.Ps Q.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf Q.Zs = Q.Dc ∧ HEq (Spf Q.Zs) Q.Sp

  spS : ∀ (u : D.what₂.Word) (x : Fin (Q.Dc.a (Q.I.wU u)) → D.what₂.LL) (y : Fin Q.S1.D → D.what₂.LL),
    Q.C.bes (Q.I.wU u) (fun i => D.what₂.embLL (x i)) (fun i => D.what₂.embLL (y i)) =
      D.besS u (D.jN u (Q.I.eNu u x)) (D.jEE (Q.I.eRR y))

structure RowsHold0 (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex) : Prop where

  zsSt : Q.Zs.Stable

  zsBl : Q.Zs.InBlock

  rows0 : ∃ R0 : IndefRows (Q.A.side Q.P0 Q.ψ0 Q.Zs), R0.toIndefData = Q.S0

  famOk : ∃ s, Q.A.fam.Ok s
  famSep : Q.A.fam.TypesSep

structure RowsHold (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex) : Prop extends RowsHold0 T Q where

  lvl : LevelLink Q.S0 Q.S1

  buRat : D.BuRational

  pkg : ∃ (N : IndefNum Q.A.fam.base) (Sc : IndefCols (Q.A.side Q.Ps Q.ψs Q.Zs) Q.Dc Q.Sp N),
    Sc.toIndefData = Q.S1 ∧ HEq Sc.col Q.C

noncomputable def RowPinS.dcF {T : TiedDataSK ex} {Q : FiniteGroupFamilyCharacterData ex} (h : RowPinS T Q) :
    ∀ Zs : DefSub Q.A.fam.amb, DefCols (Q.A.side Q.Ps Q.ψs Zs) :=
  Classical.choose h.faces

noncomputable def RowPinS.spF {T : TiedDataSK ex} {Q : FiniteGroupFamilyCharacterData ex} (h : RowPinS T Q) : ∀ Zs, SPer (h.dcF Zs) :=
  Classical.choose (Classical.choose_spec h.faces)

def SymmetricRowCompatibility (ex : Extra D L hT Gi Gl K Y cX) : Prop := ∃ (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex), RowPinS T Q

def LowerMapDetermined : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex), RowPinS T Q → RowsHold T Q →
    ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
      D.what₂.embLL (D.div.Bk u φ x) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) (D.what₂.sec D.what₂.mu0 (D.jEE x))

def PairingDetermined : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (Q : FiniteGroupFamilyCharacterData ex), RowPinS T Q → RowsHold T Q →
    ∀ u (x : Fin (Q.Dc.a (Q.I.wU u)) → D.what₂.LL) (y : Fin Q.S1.D → D.what₂.LL),
      D.what₂.embLL (Q.C.B (Q.I.wU u) x y) =
        D.what₂.perCol u D.what₂.mu0 (D.jN u (Q.I.eNu u x)) (D.what₂.sec D.what₂.mu0 (D.jEE (Q.I.eRR y)))

end Formalism.L2.Rows

end

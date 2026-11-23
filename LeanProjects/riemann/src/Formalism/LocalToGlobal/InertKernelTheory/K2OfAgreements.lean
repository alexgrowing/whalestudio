import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IntermediateMapWittQuadratic
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime]

structure RecSide {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) where

  Kr : Type
  [fieldKr : Field Kr]

  ι : Kr →+* Y.Kc

  Ψ : ℕ → Type
  [acgΨ : ∀ j, AddCommGroup (Ψ j)]
  [modΨ : ∀ j, Module Kr (Ψ j)]

  Φ : ℕ → Type

  emb : ∀ j, Φ j → Ψ j

  cmp : ∀ j, Φ j → X.Fm j

  K : ∀ j, Ψ j → Ψ (j + 1)

  KL : ∀ j, Φ j → Φ (j + 1)

  Cl : ℕ → Type
  [finCl : ∀ j, Fintype (Cl j)]

  ns : ∀ j, Cl j → ℕ

  E : ∀ j, Cl j → Φ j → Ψ (j + 1)

  Sh : ∀ j, Set (Φ j)

  Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Ψ (j + 1) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc

  e : ∀ j, ↥(Y.Rep j) ≃ Cl j

  Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc

attribute [instance] RecSide.fieldKr RecSide.acgΨ RecSide.modΨ RecSide.finCl

variable {X : Sys p} {Y : Pend X}

def TieChain (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ x : R.Φ j, X.Kz j (R.cmp j x) = R.cmp (j + 1) (R.KL j x)

def TieChainK (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ (x : R.Φ j) (y : R.Φ (j + 1)), R.emb (j + 1) y = R.K j (R.emb j x) →
    X.Kz j (R.cmp j x) = R.cmp (j + 1) y

def TieRat (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ x : R.Φ j, R.emb (j + 1) (R.KL j x) = R.K j (R.emb j x)

def RecSum (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ x ∈ R.Sh j, R.K j (R.emb j x) = ∑ c : R.Cl j, ((R.ns j c : R.Kr))⁻¹ • R.E j c x

def TieRead (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ (y : R.Φ (j + 1)) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (R.cmp (j + 1) y c' L') = R.Rd j c' L' (R.emb (j + 1) y)

def TieCls (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ La : ↥(Y.Rep j), R.ns j (R.e j La) = X.stab j La.1

def TieSer (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    Y.ThF j La (c', L') = ((Y.eS j La * (Y.eT j (c', L'))⁻¹)⁻¹ : X.G.Kf) • R.Sr j La (c', L')

def TieDel (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧
    ∀ (La : ↥(Y.Rep j)), ∀ x ∈ R.Sh j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      R.Rd j c' L' (R.E j (R.e j La) x) = cK • Y.DelF j (R.cmp j x La.1.1 La.1.2) (R.Sr j La.1 (c', L'))

def TieSpan (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, X.FQ j ≤ Submodule.span X.G.Kf (R.cmp j '' R.Sh j)

def TieSpanAll (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, X.FQ j ≤ Submodule.span X.G.Kf (Set.range (R.cmp j))

def TieUp (R : RecSide X Y) : Prop :=
  ∀ j < X.mm, ∀ y : R.Φ (j + 1), R.cmp (j + 1) y ∈ X.FQ (j + 1)

variable (X Y) in

def K2NonzeroUnit : Prop :=
  ∀ j < X.mm, ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧
    ∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2)

def K2OfAgreements : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (R : RecSide X Y),
    TieChain R → TieRat R → RecSum R → TieRead R → TieCls R → TieSer R → TieDel R → TieSpan R →
      K2NonzeroUnit X Y ∧ ∀ j < X.mm, ExpansionEquality D X Y j

def Adm3bOf : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (R : RecSide X Y),
    TieChain R → TieSpanAll R → TieUp R → adm3b D X

def KerOfSmul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (f : MvPowerSeries (X.ZA j) Y.Kc),
    Y.ThF j La La' = ((Y.eS j La * (Y.eT j La')⁻¹)⁻¹ : X.G.Kf) • f →
      ∀ G : (X.Pj j).Xsp, Y.ker j La La' G = Y.DelF j G f

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def SharpQ (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ)
    (x : ((Tw.fm u μ).lat i).V) (Q : (D.chTw u μ).cls i → MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : Prop :=
  (∀ c, Q c ∈ WtPol ℂ (nuT D u i)) ∧ ∀ c, (D.chTw u μ).sharp i ((Tw.fm u μ).emb i x c) = frPoly (t.O u μ) i (Q c)

open Classical in

def qOf (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (x : ((Tw.fm u μ).lat i).V) :
    (D.chTw u μ).cls i → MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ :=
  if h : ∃ Q, SharpQ t Tw u μ i x Q then Classical.choose h else fun _ => 0

def entRec (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i)
    (x : ((Tw.fm u μ).lat i).V) : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ :=
  fun c' y' =>
    (((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
      ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D (t.O u μ).dgen (qOf t Tw u μ i x c) ((t.O u μ).frm (i + 1) y'))
          ((t.rd u μ).Th t.seam t.amb i c c'))

def klRec (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) :
    ((Tw.fm u μ).lat i).V →ₗ[D.what₂.LL] ((Tw.fm u μ).lat (i + 1)).V :=
  Formalism.L2.G.Cmp.ratMap ((Tw.fm u μ).emb i) ((Tw.fm u μ).emb (i + 1)) ((Tw.fm u μ).emb_inj (i + 1))
    ((D.chTw u μ).Klin i)

def recOf {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) : RecSide X Y where
  Kr := ℂ
  ι := ι
  Ψ i := (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ
  Φ i := ((Tw.fm u μ).lat i).V
  emb i x := (Tw.fm u μ).emb i x
  cmp j x := cmp j x
  K i φ := (D.chTw u μ).K i φ
  KL i x := klRec Tw u μ i x
  Cl i := (D.chTw u μ).cls i
  ns i c := Nat.card ((D.chTw u μ).stab i c)
  E i c x := entRec t Tw u μ i c x
  Sh i := {x | ∃ Q, SharpQ t Tw u μ i x Q}
  Rd := Rd
  e := e
  Sr := Sr

def K2OfParams : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc),
    X.mm ≤ D.R.m → (∀ j < X.mm, (Tw.fm u μ).KRat j) →
    TieChainK (recOf X Y t Tw u μ ι σ cmp Rd e Sr) → TieRead (recOf X Y t Tw u μ ι σ cmp Rd e Sr) →
    TieCls (recOf X Y t Tw u μ ι σ cmp Rd e Sr) → TieSer (recOf X Y t Tw u μ ι σ cmp Rd e Sr) →
    TieDel (recOf X Y t Tw u μ ι σ cmp Rd e Sr) → TieSpan (recOf X Y t Tw u μ ι σ cmp Rd e Sr) →
      K2NonzeroUnit X Y ∧ ∀ j < X.mm, ExpansionEquality D X Y j

def Adm3bOfRec : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc),
    (∀ j < X.mm, (Tw.fm u μ).KRat j) →
    TieChainK (recOf X Y t Tw u μ ι σ cmp Rd e Sr) → TieSpanAll (recOf X Y t Tw u μ ι σ cmp Rd e Sr) →
    TieUp (recOf X Y t Tw u μ ι σ cmp Rd e Sr) → adm3b D X

end Rec

end Formalism.L2.KerInert.K2

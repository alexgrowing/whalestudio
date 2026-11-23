import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Formalism.LocalToGlobal.ClassRec

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev SExt : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (r : RowsT K w Z Wt p0) (col : ColT w Z), SX K B f T w Z Wt p0 r col → Type 1

def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit

def SXE (E : SExt) : SPosition := fun K B f T w Z Wt p0 r col => Σ a : SX K B f T w Z Wt p0 r col, E K B f T w Z Wt p0 r col a

structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
  R : RPosition
  N : NExt hL
  S : SExt
  Γ : GeoP

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

@[reducible] def Prm.s (p : Prm hL) : Slots := ⟨p.R, NX hL p.N, SXE p.S, OX p.Γ⟩

def WPt.core {p : Prm hL} {K : Ctx} (q : WPt p.s K) : NCore hL q.x.what₂ q.x.n := q.x.nx.1

structure SPin {p : Prm hL} {K : Ctx} (q : WPt p.s K) (S : Formalism.L2.LinkedFamilyData q.O.ex) : Prop where
  host : S.host = q.core.a.host
  cols : S.cols = q.x.col.C
  full : HEq S.full q.x.col.full
  g : HEq S.g q.x.col.g
  theta : (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) = ⟨q.x.th.provA, q.x.th.all⟩
  twE : S.twIn.E = twEOf q.O.ex.xd
  twGood : DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch S.twIn
  chr : (⟨S.n.cf, S.n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩
  gal : S.n.gal = q.core.a.all.gal
  nn : S.n.n = q.core.a.all.n
  exp : S.n.exp = q.core.a.all.exp
  chiD : S.n.chiD = q.core.a.all.chiD
  twF : S.n.twF = q.core.a.all.twF
  types : HEq S.n.types q.core.a.all.types
  cover : HEq S.n.cover q.core.a.all.cover
  plB : S.n.plB = q.core.a.all.plB
  thetaChr : HEq S.thetaChr q.x.th.chr
  dt : ∀ a, S.chrDt.eDt a = (QuotientGroup.mk a : GlobalTheory.Mem.Col2.DtQ q.B.host q.w.I.SQ)
  pieces : S.what₂.O.pieces.rcf = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.ray ∧ S.what₂.O.pieces.MDel = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.M'
  inK : S.inK = q.x.div.inK
  geo : HEq S.geo q.x.div.geo
  tw : ∃ he : q.O.ex.tw = q.w.tw q.Z, TC.StdTw q.w.I q.w.l q.Z q.w.l0 (he ▸ S.tw)

structure KPin {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex) : Prop where
  std : TC.StdKer q.w.I q.w.l q.Z t
  O : t.O = q.x.ker.O
  ent : HEq t.ent q.x.ker.E
  adapted : t.Adapted
  top : t.TopPinned

abbrev BdRec : GlobalTheory.Fc.BdT := fun _ O _ => Formalism.L2.RecT O.ex

structure RecPin {p : Prm hL} {K : Ctx} (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex) : Prop where
  s : SPin q R.T.toTiedDataS
  k : KPin q R.T.ker
  crd : ∀ u i hi, R.T.crd u i hi = 1

def ZeU (𝒮 : Slots) : Prop := ∀ (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def EntC {w : ColW B f T} {Z : w.Lt} {t : ColT w Z} {Y : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)}
    {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy} (k : KerT t Y Gy ker) : Prop :=
  ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl k.O Bs Y (w.tw Z)),
    k.E = Formalism.L2.Ker.kerEntC Pl k.O Bs h

def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker

def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)

def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)

theorem IsBuiltE.isBuilt {𝒮 : Slots} (K X f T c) (h : IsBuiltE 𝒮 K X f T c) : IsBuilt 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨b, _⟩ => ⟨b⟩) K X f T c h

theorem IsGoodE.isGood {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsGood 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨⟨b, _⟩, g⟩ => ⟨⟨b⟩, g⟩) K X f T c h

theorem IsGoodE.isBuiltE {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsBuiltE 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ h => h.1) K X f T c h

def MemberE (𝒮 : Slots) : Prop :=
  BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)

def WitExE (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGoodE 𝒮) → ∃ q : WPt 𝒮 K, q.Is β.D β.O ∧ EntC q.x.ker

structure RecPinE {p : Prm hL} {K : Ctx} (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex) : Prop extends RecPin q R where
  entC : EntC q.x.ker
  std : GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O R.T.ker
  rd : GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z R.T.ker

def LinkR (p : Prm hL) : GlobalTheory.Fc.LkT BdRec := linkOf (𝒮 := p.s) (Bd := BdRec) fun _ q _ R => RecPinE (p := p) q R

def RecExE (p : Prm hL) : Prop := GlobalTheory.Fc.ExB (IsGoodE p.s) (LinkR p)

@[reducible] def prmR (N : NExt hL) (S : SExt) (Γ : GeoP) : Prm hL := ⟨RX, N, S, Γ⟩

end GlobalTheory.Mem.Top.Bl

end

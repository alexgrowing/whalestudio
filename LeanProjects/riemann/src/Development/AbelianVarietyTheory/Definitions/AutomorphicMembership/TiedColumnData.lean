import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.UnitaryNorms.CharGal
import Formalism.LocalToGlobal.UnitaryNorms.DefsDatum
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
import Formalism.LocalToGlobal.JointCharacters.SameChr
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.factResChar

inductive IsRecG (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Forms0 D u) : Prop
  | intro
    (D0 : D7)
    (Lc : ∀ u, ColLevel D0.R D0.host.F D0.host.E D0.sp D0.host.g (D0.mem u).C (D0.mem u).A (D0.clsLat u))
    (I : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      LocId (Lc u) (D0.what₂.places.resChar w) (nOrb (zH D0.R.toFrame (hP D0 (D0.what₂.places.resChar w))))
      (WQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w)))
      (QQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w))))
    (ψ : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D0.what₂.places.resChar w) →* (ORec D0 w (nFr D0 (D0.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D0 Lc I ψ u w h).gat (rSc sc D0.R.k (D0.what₂.places.resChar w))
      (epSc D0.R sc 1 (D0.what₂.places.resChar w))).d = Module.finrank ℂ (D0.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D0 sc 1 Lc I ψ hd))
    (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D0.what₂.Word, Forms0 (recC D0 sc 1 Lc I ψ hd) u)
    (B : GL (Fin D0.R.k) D0.host.E)
    (hBs : Cmp.StdB (recC D0 sc 1 Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D0.host.F)) (h : ((D0.what₂.places.resChar w : ℕ) : 𝓞 D0.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D0.host.F) (w'.adicCompletion D0.host.F))) B)
    (iK : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      KfRec D0 w (nFr D0 (D0.what₂.places.resChar w)) →+* ℂ_[D0.what₂.places.resChar w])
    (lam : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D0.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D0.what₂.LL), iK u w hg (embRec D0 w (nFr D0 (D0.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D0.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D0 Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (CH : CmpHyp0P T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB))
    (eq : (⟨D, Gt, c, H, F⟩ : Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
      ⟨recC D0 sc 1 Lc I ψ hd, gatTiesC D0 sc 1 Lc I ψ hd,
      Cmp.latCmpC T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB)
        (CH.toHyp0 fun u w hg v s x => pos_C D0 sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x).toHyp, H0, T⟩)
    : IsRecG sc D Gt c H F

end Rec

def Half (B : Base) (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) : Prop :=
  ∀ v v' (p : ℕ), p.Prime → (p : 𝓞 B.host.F) ∈ v.asIdeal → (p : 𝓞 B.host.F) ∈ v'.asIdeal →
    (Pv v).under (𝓞 B.host.K) = (Pv v').under (𝓞 B.host.K)

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure ColPin (w : ColW B f T) : Type where
  isTw : TC.IsTw w.I
  jets : ColIn.JetsIn w.I
  hX : B.fields.Ok
  above : ∀ v, w.I.sel v ∈ aboveF (L := B.host.E) B.host.F v
  half : Half B w.I.sel
  d3b : PlacesOverCommonPrime B.host
  selectedPlacesAgree : (∀ v hv, w.I.sel v = d3b.P v hv) ∧ ∀ v hv, w.I.sel v = d3b.P' v hv
  vals : ∀ a P, (w.I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((w.I.xi a).val P : ℂˣ) : ℂ)
  roots : ∀ a, ∀ P ∈ w.I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal))

def Pinned : WP := fun _ _ _ _ w => Nonempty (ColPin w)

structure ColumnDataSplitPrimes (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends ColT w Z where
  isRec : IsRecG K.s (w.D Z) Gt cmp g.herm g.forms
  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ

def GIs2 (K : Ctx) (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩)

structure NchT (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) : Type where
  tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch
  xi : tp.xi = w.I.xi
  psi : tp.psi = T.psi
  tie : NChTie (w.D Z) nch
  Q : ∀ v ∈ Wt, nch.Q v = T.Q v ∧ nch.k' v = T.k v
  chrPsi : PsiChoiceCompatible (w.D Z) (TC.cf w.I w.l Z) nch tp

abbrev KerFam (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (tw : TwForms D) (Gy : G.LatInst D) : Type _ :=
  ∀ u v (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)),
    haveI : Fact (D.what₂.places.resChar v).Prime := ⟨D.what₂.places.resChar_prime v⟩
    LocalToGlobal₂ D Gt cmp tw u v h (Gy.Ch u v h)

structure KerT {w : ColW B f T} {Z : w.Lt} (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) : Type 1 where
  O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)
  std : TC.StdO w.I w.l Z Y.Qp O
  unf : ∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i
  E : KerEnt (w.D Z) Y (w.tw Z)
  ok : TC.EntOk E O
  lam : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    (ker u v h).lam = E.lam v
  served : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    ThAtServed (ker u v h) E
  iw : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v h (ker u v h)
  iw_pos : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    Formalism.L2.Herm.GIwPos u v h (ker u v h)

structure DivT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) :
    Type 1 where
  Qp : TC.QpIs w.I Y.Qp
  chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) nch n.tp Y
  loc : Formalism.L2.DIV.QLocTiedC chr w.I.sel
  inK : Y.Lev → ℕ → Prop
  geo : Formalism.L2.Geo.GeoTiedP Y inK

structure ThT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (th : ThetaX (w.D Z)) :
    Type 1 where
  provA : TH.ProvA
  all : Formalism.L2.Theta.AllTied (w.D Z) th provA
  weq : Formalism.L2.Theta.WeilCompatibleEquivariance all.W
  chr : ThetaChrTied (w.D Z) (TC.cf w.I w.l Z) nch n.tp th
  same : Formalism.L2.JoinChr.SameChr all.T chr
  std : Formalism.L2.Theta.IsStdChar (w.D Z) all.W.ψ (-1)
  io : th.TieIo

def RetwistW (p : WP) (P P' : CP) : Prop :=
  Pass KPx (positionOf P) fun K B f T => ∃ w : ColW B f T, p K B f T w ∧ ∀ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c →
    DQ.TwAllAt (w.D Z) c.O.nch c.O.xd ∧ P' K B f T w Z c

theorem GIs2.gIs {w : ColW B f T} {G : GJStage B w.C} (h : GIs2 K w G) : GIs K w G := fun W V S N =>
  let ⟨a, b, ⟨t⟩⟩ := h W V S N; ⟨a, b, ⟨t.toColT⟩⟩

end GlobalTheory.Mem.Top.Bl

end

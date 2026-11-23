import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.L2.Host (CharFrame HChar TupTied)
open GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug

namespace GlobalTheory.PlugPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Side (D : D7) (nch : NChoice D) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  J : CoreJ D
  [alg : Algebra J.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 J.Q.c.F
  P0 : Subgroup G
  ψ0 : P0 →* D.what₂.LLˣ
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec
  S : NX.RatDat D.ntw
  YS : NX.NExpRealS R cG S
  cf : CharFrame D
  tp : TupTied D cf nch

attribute [instance] Side.grp Side.fin Side.alg

namespace Side

variable {D : D7} {nch : NChoice D} (s : Side D nch)

def upd (kap : ℝ) (lam : type_of% s.R.lam3) (err : type_of% s.R.err0) : Side D nch :=
  { s with R := (s.R.updS kap lam).withErr err, YS := { s.YS with } }

structure Ties (EX : ErrX D) (xd : ThData D) : Prop where
  frame : s.R.C = s.cf
  tied : Tied EX s.J s.cf
  series : Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀)
  level : LevelIs D.nexp (s.R.eG.trans s.cG) s.P0 s.ψ0⁻¹
  data : AllData D.nexp xd.xd0
  psi : Formalism.L2.Host.PsiChoiceCompatible D s.cf nch s.tp
  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (s.tp.psi w).ValuesIn 0 D.what₂.embLL
  small : SmallHas D s.cf
  types : GlobalTheory.DimPartsCompare.TameTie D s.cf.W.om

def Export (xd : ThData D) : Prop :=
  Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) ∧ LevelIs D.nexp (s.R.eG.trans s.cG) s.P0 s.ψ0⁻¹ ∧ AllData D.nexp xd.xd0

def Rays : Prop := ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel s.R.toRealDat t)

end Side

abbrev BdPt : BdT := fun _ O c => PtAt O.ex c

def sidePt {D : D7} {O : Obj D} {c : ℝ} (b : BdPt D O c) : Side D O.ex.nch :=
  { G := b.P.Gp, Pl0 := b.P.Pl0, I0 := b.P.I0, T := b.P.T, A3 := b.P.A3, J := b.T, R := b.R, P0 := b.P.P0, ψ0 := b.P.ψ0, cG := b.cG,
    v₀ := b.v₀, S := b.Sx, YS := b.nexp, cf := b.R.C, tp := b.Tp }

def cfPt (D : D7) (O : Obj D) (c : ℝ) (b : BdPt D O c) : BdCF D O c := ⟨b.T, b.R.C⟩

section Wit

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

def sideOf {hL : GlobalTheory.Published.LocalLanglandsGL} (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (c : NCore hL t n) : Side (w.st Z).toD7 nch :=
  { G := _, Pl0 := _, I0 := _, T := _, A3 := _, J := t.r.z.core, R := t.r.z.R, P0 := t.r.z.F.P0, ψ0 := t.r.z.F.ψ0, cG := t.r.z.cG,
    v₀ := t.r.z.geo.v₀, S := _, YS := c.row.nexp, cf := GlobalTheory.Mem.Col2.TC.cf w.I w.l Z, tp := n.tp }

end Wit

def ExpE (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ _ _ _ _ _ _ _ t _ n xd c =>
  PLift ((sideOf t n c).Export xd) × PUnit.{2}

structure NRead (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) : Type 2 where
  rd : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (xd : ThData (w.D Z)),
    𝒮.Nx K B f T w Z Wt p0 t nch n xd → NX hL (ExpE hL) K B f T w Z Wt p0 t nch n xd

def HasExp {hL : GlobalTheory.Published.LocalLanglandsGL} (E : NExt hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (ExpE hL K B f T w Z Wt p0 t nch n xd c)

def NRead.of {hL : GlobalTheory.Published.LocalLanglandsGL} (Rx : RPosition) {E : NExt hL} (h : HasExp E) (Sx : SPosition) (Ox : OComponent₂) :
    NRead hL ⟨Rx, NX hL E, Sx, Ox⟩ :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨y.1, Classical.choice (h _ _ _ _ _ _ _ _ _ _ _ _ _ y.2)⟩⟩

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {𝒮 : Slots}

def sideW (ν : NRead hL 𝒮) {K : Ctx} (p : WPt 𝒮 K) : Side (p.w.D p.Z) p.O.ex.nch :=
  sideOf p.x.what₂ p.x.n (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).1

def pinPt (ν : NRead hL 𝒮) : PinT 𝒮 BdPt := fun _ p _ b => ∃ kap lam err, sidePt b = (sideW ν p).upd kap lam err

def RayRec (D : D7) (nch : NChoice D) : Prop :=
  ∀ (w : D.what₂.places.Pl) (S : Finset (Pl D.host.E)),
    (∀ P ∈ S, (((D.host.pde * D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ (Nat.card (kP P)).Prime) ∨
      (D.what₂.muAt w ≠ D.what₂.mu0 ∧ P ∈ nch.Q w)) →
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D)
      (D.host.g 0 * D.host.g 1 * ∏ q ∈ S.image (fun P => Nat.card (kP P)), q)

def RayPosition : V4.Slot := fun _ X _ _ c => RayRec X.toD7 c.O.nch

def TiesB : BdP BdPt := fun _ O _ b => (sidePt b).Ties O.ex.errX O.ex.xd ∧ (sidePt b).Rays

def MoreAlong (𝒜 : FamClass) (σ : RawSel BdPt 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : 𝒜 Fm, ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    SingleIndexPlacesAreTwisted (σ Fm hc x hx i) → More (σ Fm hc x hx i)

def RowsAlong (𝒜 : FamClass) (σ : RawSel BdPt 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : 𝒜 Fm, ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, (σ Fm hc x hx i).Rows

def OntoAlong (𝒜 : FamClass) (σ : RawSel BdPt 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : 𝒜 Fm, ∃ C0 : ℝ, 0 ≤ C0 ∧ ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (C : ℝ),
    C0 ≤ C → DIVinN Fm → ((σ Fm hc x hx i).S false).ON ((σ Fm hc x hx i).N C CH)

end GlobalTheory.PlugPt

end

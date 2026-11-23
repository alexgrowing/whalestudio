import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.Joint0

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

def PrePin (P : Pre) : Prop :=
  letI := P.host.cmStar; ∀ (a : Fin P.sp.X'.rank) (b : Fin (P.sp.X P.R.m).rank), (a : ℕ) = b →
    P.sp.iX' (P.sp.X'.frame a) = (P.sp.X P.R.m).frame b

def KPx : BaseP := fun B f => (∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f) ∧ PrePin B.toPre

structure ColW (B : Base) (f : Fr B.toPre) (T : TwDat B) : Type 1 where
  px : PreX B.toPre
  I : ColIn B px
  ok : I.Ok
  C_eq : I.C = f
  S_eq : I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'}
  xi_range : Set.range I.xi = T.set f
  pins : TC.Pins B px
  l : TC.Laws I
  l0 : TC.Law0 I l
  δ : Fld.FieldDat B.toPre
  exact : B.KsExact δ f
  fld : GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE
  val : ∀ C W V S N G, ValLL0 (assemble B C W V S N G) (Fr.at ⟨B, C, W, V, S, N, G⟩ f)

namespace ColW

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

abbrev C : Cols B := TC.cols w.I w.l

abbrev Lt : Type _ := TC.Later B w.C

abbrev st (Z : w.Lt) : Stages := ⟨B, w.C, Z.W, Z.V, Z.S, Z.N, Z.G⟩

abbrev D (Z : w.Lt) : D7 := TC.rec7 w.I w.l Z

abbrev tw (Z : w.Lt) : TwForms (w.D Z) := TC.tw w.I w.l w.l0 Z

end ColW

abbrev WP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), ColW B f T → Prop

abbrev ZP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop

abbrev CP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), V4.Core K (w.st Z) f T → Prop

def positionOf (P : CP) : V4.Slot := fun K X f T c =>
  ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
    (⟨X.C, ⟨X.W, X.V, X.S, X.N, X.G⟩, c⟩ : Σ (C : Cols X.B) (Y : TC.Later X.B C), V4.Core K ⟨X.B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T) =
      ⟨w.C, Z, c'⟩

def HasZ (P : ZP) : WP := fun K B f T w => ∃ Z : w.Lt, P K B f T w Z

def HasC (P : CP) : WP := fun K B f T w => ∃ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c

def StepW (p q : WP) : Prop :=
  Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, p K B f T w → q K B f T w

structure ColT {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) : Type 1 where
  C : Formalism.L2.Forms.ColsTiedSym (w.D Z)
  std : TC.StdC w.I w.l Z C
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)
  full : Formalism.L2.Forms.ColsFullS C
  stdDt : TC.StdDt w.I w.l Z full.1.base.dt
  Gt : GatTies (w.D Z)
  cmp : LatCmp (w.D Z)
  g : Formalism.L2.G.GroupCompatibilityAll (w.D Z) Gt cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (C.forms u).to0
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) full.1.base.toHermColsCh full.1.g Gt

def GIs (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColT w ⟨W, V, S, N, G⟩)

structure ColT.Objs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} (t : ColT w Z)
    (c : V4.Core K (w.st Z) f T) : Prop where
  xi : c.xi = w.I.xi
  lev : c.O.lev = t.full.1.base.lev0
  errX : c.O.errX = Formalism.L2.Herm.toErrXS t.full.1
  tw : c.O.tw = w.tw Z
  gatT : c.O.gatT = t.Gt
  cmp : c.O.cmp = t.cmp

theorem positionOf_intro {P : CP} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (h : P K B f T w Z c) : positionOf P K (w.st Z) f T c := ⟨w, Z, c, h, rfl⟩

theorem positionOf_ind {P : CP} {R : V4.Slot}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c → R K (w.st Z) f T c)
    {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (hc : positionOf P K X f T c) : R K X f T c := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  dsimp only at f T
  obtain ⟨w, Z, c', hp, e⟩ := hc
  exact Eq.mpr (congrArg (fun y : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T =>
    R K ⟨B, y.1, y.2.1.W, y.2.1.V, y.2.1.S, y.2.1.N, y.2.1.G⟩ f T y.2.2) e) (h K B f T w Z c' hp)

theorem positionOf_mono {P P' : CP} (h : ∀ K B f T w Z c, P K B f T w Z c → P' K B f T w Z c) (K : Ctx) (X : Stages) (f : Fr X.B.toPre)
    (T : TwDat X.B) (c : V4.Core K X f T) (hc : positionOf P K X f T c) : positionOf P' K X f T c :=
  let ⟨w, Z, c', hp, e⟩ := hc; ⟨w, Z, c', h _ _ _ _ _ _ _ hp, e⟩

theorem StepW.of_all {p q : WP} (h : ∀ K B f T w, K.Over B.toPre → Forced K B T → p K B f T w → q K B f T w) : StepW p q :=
  Step.of_all fun K B f T a _ b _ w => h K B f T w a b

theorem StepW.trans {p q r : WP} (h : StepW p q) (h' : StepW q r) : StepW p r :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => H.2 w (H.1 w a))

theorem StepW.and {p q r : WP} (h : StepW p q) (h' : StepW p r) : StepW p fun K B f T w => q K B f T w ∧ r K B f T w :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => ⟨H.1 w a, H.2 w a⟩)

theorem step_hasCore {admitted : AtP} {p : WP} {P : CP} (h0 : Step KPx admitted fun K B f T => ∃ w : ColW B f T, p K B f T w)
    (h1 : StepW p (HasC P)) : Step KPx admitted (HasCore (positionOf P)) :=
  (h0.and ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans h1)).trans (Step.of_all fun _ _ _ _ _ _ _ H =>
    let ⟨w, a⟩ := H.1
    let ⟨Z, c, hc⟩ := H.2 w a
    ⟨w.C, Z.W, Z.V, Z.S, Z.N, Z.G, c, positionOf_intro hc⟩)

end GlobalTheory.Mem.Top.Bl

end

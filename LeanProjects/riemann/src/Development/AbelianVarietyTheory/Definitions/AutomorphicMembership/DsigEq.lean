import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure GoodO (D : D7) (nch : NChoice D) (xd : ThData D) : Prop where
  tw : ∃ I : TwIn D, I.E = twEOf xd ∧ DQ.GoodAllAt D nch I ∧ GlobalTheory.HeightCounting.GoodCl D nch I
  sep : ∀ v v', D.what₂.muAt v ≠ D.what₂.mu0 → D.what₂.muAt v' ≠ D.what₂.mu0 → nch.twI v ≠ nch.twI v' → Disjoint (nch.Q v) (nch.Q v')

def GoodC (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltC 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsGood (𝒮 : Slots) : V4.Slot := positionOf (GoodC 𝒮)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure Wit (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  isOver : K.Over B.toPre
  forced : Forced K B T
  Wt : Set B.places.Pl
  pin : ColPin w
  coh : Coh B T
  vol : Formalism.L2.Theta.VolTieG (w.D Z)
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z Wt O.p0
  rx : 𝒮.Rx K B f T w Z Wt O.p0 what₂
  lev : O.lev = col.full.1.base.lev0
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z Wt O.nch
  nx : 𝒮.Nx K B f T w Z Wt O.p0 what₂ O.nch n O.xd
  sx : 𝒮.Sx K B f T w Z Wt O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT O.X O.Gy ker0
  div : DivT n O.X
  th : ThT n O.th
  obj : ObjT O what₂
  ox : 𝒮.Ox K B f T w Z Wt O what₂
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  gauge : O.gauge.IsGauge
  good : GoodO (w.D Z) O.nch O.xd

def Built.wit {𝒮 : Slots} {K : Ctx} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c)
    (h : GoodO (w.D Z) c.O.nch c.O.xd) : Wit 𝒮 K w Z c.O :=
  { b with isOver := c.isOver, forced := c.forced, Wt := c.Wt, vol := (b.g Z.W Z.V Z.S Z.N).1, real := c.real, dsig_eq := c.dsig_eq,
           gauge := c.gauge_def, good := h }

structure WPt (𝒮 : Slots) (K : Ctx) : Type 1 where
  B : Base
  f : Fr B.toPre
  T : TwDat B
  w : ColW B f T
  Z : w.Lt
  O : Obj (w.D Z)
  x : Wit 𝒮 K w Z (ofObj O)

def WPt.Is {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) (D : D7) (O : Obj D) : Prop := (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨p.w.D p.Z, p.O⟩

abbrev PinT (𝒮 : Slots) (Bd : GlobalTheory.Fc.BdT) : Type 1 := ∀ (K : Ctx) (p : WPt 𝒮 K) (c : ℝ), Bd (p.w.D p.Z) p.O c → Prop

def linkOf {𝒮 : Slots} {Bd : GlobalTheory.Fc.BdT} (P : PinT 𝒮 Bd) : GlobalTheory.Fc.LkT Bd := fun K β c b =>
  ∃ (p : WPt 𝒮 K) (b' : Bd (p.w.D p.Z) p.O c), P K p c b' ∧
    (⟨β.D, β.O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨p.w.D p.Z, p.O, b'⟩

def WitEx (𝒮 : Slots) : Prop := ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGood 𝒮) → ∃ p : WPt 𝒮 K, p.Is β.D β.O

end GlobalTheory.Mem.Top.Bl

end

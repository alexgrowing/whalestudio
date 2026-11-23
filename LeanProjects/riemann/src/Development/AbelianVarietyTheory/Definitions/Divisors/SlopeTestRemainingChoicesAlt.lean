import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.TestLat

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Numbers

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
  {K K' : Type} [Field K] [Field K']

def BottomsWith (Q : ℂ → Prop) : Prop :=
  ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
    IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ Q (P.norm : ℂ) ∧ Q (P'.norm : ℂ)

structure SqIn (σ : K →+* ℂ) : Prop where

  norms : BottomsWith G μ₀ (fun _ => True) → BottomsWith G μ₀ fun z => z ∈ Set.range σ

  toric : ∀ (i j : Fin D.R.m) (s : ℕ) (c : Bool) (x y : ℂ), 1 ≤ s → s ≤ halfRank D i j → IsTor G i j s (nuH G μ₀ i j) x →
    IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y → y / x ∈ Set.range σ

variable {G μ₀}

theorem SqIn.mono {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SqIn G μ₀ σ) (hσ : Set.range σ ⊆ Set.range σ') : SqIn G μ₀ σ' :=
  ⟨fun a => let ⟨δ, t0, b⟩ := h.norms a
    ⟨δ, t0, fun ij => let ⟨P, P', c⟩ := b ij; ⟨P, P', c.1, hσ c.2.1, hσ c.2.2⟩⟩,
    fun i j s c x y a b d e => hσ (h.toric i j s c x y a b d e)⟩

end Numbers

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure SlopeTestRemainingChoices (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (W : G.Weil) (n : ℕ) where

  M : Vol G

  ρ : G.RealVec

  ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W

  cv : ChainVec p.R.toRealDat

  rm : RealMatch W

  S : SumChoice W Set.univ

  rp : ClassReps G

  e : Fin n ≃ TestIx G × VVIdx (LaP G)

  c : Fin D.R.m → Fin D.R.m → p.P.T → ℂ

def SlopeTestRemainingChoices.ch {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Choice p.R.toRealDat :=
  ⟨⟨1, CF, p.Z.b⟩, G, W, a.M, a.ρ, a.ξ, a.cv, a.rm, a.S, a.rp, n, a.e, a.c⟩

theorem SlopeTestRemainingChoices.atScale {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) :
    a.ch.AtScale CF p.Z.b := rfl

structure SlopeTestRemainingChoices.OK {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Prop where

  is : a.ch.Is

  eser : GlobalTheory.GLq.ESerTie D

  field : a.ch.FieldOK

  sq : SqIn G p.P.A3.A.μ0 D.what₂.embLL

def Fld : FldT := fun p _ G W => ∃ (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK

end GlobalTheory.BigTop.Fun

end

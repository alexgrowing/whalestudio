import Formalism.SharpRestriction.LevelLetterCocycles.InvLevCoreOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

attribute [instance] LevBasics.fF LevBasics.algOF

def LevDiv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w

def LevRat (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ d ≠ 0) → ∀ c : F,
    (∀ ζ : Rs F PD.p s, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

def levEv_of (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (hD : LevDiv W a s hB.F hB.ev)
    (hR : LevRat W a s hB.F hB.ev) : LevEv W a s where
  F := hB.F
  fF := hB.fF
  algOF := hB.algOF
  hp := hB.hp
  ev := hB.ev
  ev_O := hB.ev_O
  ev_letE := hB.ev_letE
  ev_ps := hB.ev_ps
  ev_pt := hB.ev_pt
  σ := hB.σ
  ev_γ := hB.ev_γ
  gen := hB.gen
  div := hD
  rat := hR

theorem invLevCore_of_parts (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hB : ∀ a s, LevBasics W a s)
    (hD : ∀ a s, LevDiv W a s (hB a s).F (hB a s).ev) (hR : ∀ a s, LevRat W a s (hB a s).F (hB a s).ev)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W :=
  invLevCore_of W hπ (fun a s => levEv_of W a s (hB a s) (hD a s) (hR a s)) hPC

end Parts

end Formalism.MainNotions.UnusedSlot80.InvW

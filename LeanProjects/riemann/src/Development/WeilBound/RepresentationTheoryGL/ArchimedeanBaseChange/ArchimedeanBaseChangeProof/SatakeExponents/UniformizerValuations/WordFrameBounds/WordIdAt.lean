import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev LL (d : LocData E n) : Type := Unit ⊕ Unit ⊕ ({w : Pl E // d.Good w} × ℕ × Bool × Bool)

def locL (d : LocData E n) (a : ℕ) (ha : a ≤ n) : LL d → LM d.kap a (n - a)
  | .inl _ => d.betaL a ha
  | .inr (.inl _) => d.eL a
  | .inr (.inr x) => if x.2.2.2 then (d.hL a ha x.1.1 x.2.1 x.2.2.1).adj else d.hL a ha x.1.1 x.2.1 x.2.2.1

def atPlace (d : LocData E n) (w : Pl E) (ls : List (LL d)) : List (ℕ × Bool × Bool) :=
  ls.filterMap fun p => match p with
    | .inr (.inr x) => if x.1.1 = w then some x.2 else none
    | _ => none

def prodL (d : LocData E n) (ls : List (LL d)) (a : ℕ) : LM d.kap a (n - a) :=
  if ha : a ≤ n then (d.fixL a :: ls.map (locL d a ha)).foldr LM.mul (d.eL a) else d.eL a

def LocWord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n)
  (ls : List (LL d)) (N : ℕ), ls.countP Sum.isLeft = N + 1 →
  (∀ p, (locL d a ha p).Ok d.P ∧ ((d.eL a).mul (locL d a ha p)).Eqv d.P (locL d a ha p) ∧ d.IsLetter a ha (locL d a ha p)) ∧
  (∀ w ∈ d.B, (prodL d ls a).tr d.P d.one w = ((d.fixL a).mul (MLM.pw (d.betaL a ha) N)).tr d.P d.one w) ∧
  (∀ w ∉ d.B, (prodL d ls a).s w = (MLM.wordLS d a ha w (atPlace d w ls)).s w ∧
    (prodL d ls a).t w = (MLM.wordLS d a ha w (atPlace d w ls)).t w) ∧
  ∀ w, ¬ d.Good w → atPlace d w ls = []

def LocMatch : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  MLM.MOk d → ∀ (S : Set (Pl E)), IsSection S → U.LevelOff S d.B d.KU → d.T.Nonempty → (∀ w u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) →
  (∀ w ∈ S, w ∉ d.B → IsSplitAt w → d.Good w) → ∀ (ls : List (LL d)) (m k : ℕ), 1 ≤ m → 1 ≤ k → ls.countP Sum.isLeft = m * k →
  ∀ lU : List (U.UGen E n), (∀ w ∉ d.B, U.UGen.sph lU w = MLM.wordUS d w (atPlace d w ls)) →
  (∀ w ∈ d.B, IsHecke (d.KU w) (d.gU m w)) ∧
  (∃ w ∈ S, ∀ y, U.fam d.B d.KU (d.gU m) k lU w y ≠ 0 → y.1.val.charpoly.Separable) ∧
  ∀ a ≤ n, (IsTestP ((prodL d ls a).tr d.P d.one) ∧ IsTestP (prodL d ls a).t ∧
    IsTestP (seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t) ∧
    ∀ w ∈ S, Match n a (n - a) w (d.μ w) (U.fam d.B d.KU (d.gU m) k lU w) (seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w)) ∧
    ∃ w ∈ S, ¬ IsSplitAt w ∧ RegAt2 a (n - a) w ((prodL d ls a).tr d.P d.one w)

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

def gl (i : F₀.C.ι) (p : F.Γ × Bool) : BGen (F.B i) := if p.2 then (F.g p.1 i).adj else F.g p.1 i

def ul (p : F.Γ × Bool) : U.UGen E n := if p.2 then (F.ug p.1).adj else F.ug p.1

def bw (i : F₀.C.ι) (w : List (F.Γ × Bool)) : List (BGen (F.B i)) := List.replicate F.m (Sum.inr (F.β i)) ++ w.map (gl F i)

def MM (i : F₀.C.ι) : Matrix (F.B i).I (F.B i).I ℂ := opM (F₀.A i).Ta (F₀.A i).Tb (tenN F.d.P (F.B i) (Equiv.refl _) F.d.one)

def tw (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) : PT (F.B i) :=
  BGen.wd (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten) (F.t₂ i)

def WordIdAt : Prop := ∃ (cc : F₀.C.ι → ℂ) (c₀ : F₀.C.ι → ℝ), (∀ i, 0 ≤ c₀ i) ∧ ∀ ws : List (List (F.Γ × Bool)), ws ≠ [] →
  (∀ i, D4.IsTest2J (trM (tw F i ws).Φ (MM F i)) (c₀ i * (1 + (tw F i ws).T) + (tw F i ws).r)) ∧
  LinearMap.trace ℂ _ ((F.R.u ^ ws.length * ((ws.flatten.map (ul F)).map F.R.op).prod :
      EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
      EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
    ∑ i, cc i * (BGen.sc (ws.map (bw F i)).flatten *
      ellSum2 (F₀.C.μG (F₀.C.a i)) (F₀.C.μG (n - F₀.C.a i)) (trM (tw F i ws).Φ (MM F i)))

end Frame

def WordId : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct → WordIdAt F

end PositivityTheory.Rg.BcB.F.B3

end

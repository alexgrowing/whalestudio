import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.MLM

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def CtStar : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
  ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, (∀ u, ‖((μ u : ℂˣ) : ℂ)‖ = 1) → ∀ f : UL n w → ℂ, IsHecke (KL n w) f →
    ctMu (Nat.add_sub_cancel' ha) w μ (PositivityTheory.Rg.BcB.F.Eig.lstar f) = lfStar (ctMu (Nat.add_sub_cancel' ha) w μ f)

def wordLS (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (l : List (ℕ × Bool × Bool)) : LM d.kap a (n - a) :=
  l.foldr (fun x L => (if x.2.2 then (d.hL a ha w x.1 x.2.1).adj else d.hL a ha w x.1 x.2.1).mul L) (d.eL a)

def wordUS (d : LocData E n) (w : Pl E) (l : List (ℕ × Bool × Bool)) : UL n w → ℂ :=
  l.foldr (fun x f => PositivityTheory.Rg.BcB.F.Eig.lconv (if x.2.2 then PositivityTheory.Rg.BcB.F.Eig.lstar (d.hU w x.1) else d.hU w x.1) f)
    ((KL n w : Set (UL n w)).indicator 1)

def MatchLMWordS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (w : Pl E), d.Good w → (∀ u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) → ∀ l : List (ℕ × Bool × Bool),
    Match n a (n - a) w (d.μ w) (wordUS d w l)
      (PositivityTheory.Rg.BcN.F2.mconv ((wordLS d a ha w l).tr d.P d.one w) ((wordLS d a ha w l).t w))

def MatchLMWordSOf : Prop := MT.MatchSplit → MT.CtMul → CtStar → SphComm → IdemAlg → MatchLMWordS

def MuInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ), Match n a b w μ f φ ↔ Match n a b w μ' f φ

def RegPowT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok → MOk d →
  ∀ (a : ℕ) (ha : a ≤ n) (m : ℕ), ∀ w ∈ d.T, RegAt2 a (n - a) w (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w)

def SepPowT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok → MOk d →
  ∀ (m : ℕ), ∀ w ∈ d.T, ∀ y, d.gU (m + 1) w y ≠ 0 → y.1.val.charpoly.Separable

def MacInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → MOk d →
  ∀ (a : ℕ) (ha : a ≤ n), ∀ w ∈ d.S₀, ∀ x y : d.kap w, IsHecke (d.L a w) ((d.betaL a ha).m w x y) ∧
    ∀ m : ℕ, PositivityTheory.Rg.BcN.F2.mconv ((((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w)) (idem (d.L a w)) =
      ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w

def SplitPlaceGeneratorPowers : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → MOk d →
  ∀ w ∈ d.S₀, ∀ (N : ℕ) (u : UL n w), d.gU (N + 1) w u = MS.gpow (d.e w) N (u : GLw n w)

def MacInvOf : Prop := (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], PositivityTheory.Rg.BcN.F2.LocOpUniformizer E) → IdemAlg → MacInv
def SplitPowersOfIdempotents : Prop := IdemAlg → SplitPlaceGeneratorPowers

def MatchLMB3Of : Prop := MT.MatchT → MS.MatchSplitPlace → MB.MatchBadS → MB.MatchBadI → MB.FixIdem → IdemAlg → MatchLMB2

end PositivityTheory.Rg.BcB.F.MLM

end

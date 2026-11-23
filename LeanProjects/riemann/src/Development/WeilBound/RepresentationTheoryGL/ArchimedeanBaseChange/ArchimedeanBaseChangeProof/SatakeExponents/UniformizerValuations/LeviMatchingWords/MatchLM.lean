import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchB
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchS

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.MLM

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pw {κ : Pl E → Type} [∀ w, Fintype (κ w)] {a b : ℕ} (L : LM κ a b) : ℕ → LM κ a b
  | 0 => L
  | k + 1 => L.mul (pw L k)

def muAt (d : LocData E n) (w : Pl E) : (w.adicCompletion E)ˣ →* ℂˣ := if w ∈ d.S₀ ∨ (w ∈ d.Bad ∧ IsSplitAt w) then d.μ w else 1

def MatchLMB : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (m : ℕ), ∀ w ∈ d.B,
    Match n a (n - a) w (muAt d w) (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w)

def MatchLMGood : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (w : Pl E), d.Good w → ∀ (k j : ℕ) (intersection_update_fsHerm_neg_one : Bool),
    Match n a (n - a) w (d.μ w) (U.lpow (KL n w) (d.hU w k) (j + 1))
      ((pw (d.hL a ha w k intersection_update_fsHerm_neg_one) j).tr d.P d.one w)

def MatchLMUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (w : Pl E), w ∉ d.B → (IsSplitAt w → d.Good w) →
    Match n a (n - a) w (if IsSplitAt w then d.μ w else 1) ((KL n w : Set (UL n w)).indicator 1) ((d.eL a).tr d.P d.one w)

def MatchLMId : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (L : LM d.kap a (n - a)), (L = d.betaL a ha ∨ L = d.fixL a ∨ d.IsGen a ha L) →
    (L.mul (d.eL a)).Eqv d.P L ∧ ((d.eL a).mul L).Eqv d.P L

def MatchLMIdOf : Prop := IdemAlg → LocOk → MatchLMId

def wordL (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (l : List (ℕ × Bool)) : LM d.kap a (n - a) :=
  l.foldr (fun x L => (d.hL a ha w x.1 x.2).mul L) (d.eL a)

def wordU (d : LocData E n) (w : Pl E) (l : List (ℕ × Bool)) : UL n w → ℂ :=
  l.foldr (fun x f => PositivityTheory.Rg.BcB.F.Eig.lconv (d.hU w x.1) f) ((KL n w : Set (UL n w)).indicator 1)

def MatchLMWord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  ∀ (a : ℕ) (ha : a ≤ n) (w : Pl E), d.Good w → ∀ l : List (ℕ × Bool),
    Match n a (n - a) w (d.μ w) (wordU d w l)
      (PositivityTheory.Rg.BcN.F2.mconv ((wordL d a ha w l).tr d.P d.one w) ((wordL d a ha w l).t w))

def MatchLMWordOf : Prop := MT.MatchSplit → MT.CtMul → SphComm → IdemAlg → MatchLMWord
def MatchLMBOf : Prop := MT.MatchT → MS.MatchSplitPlace → MB.MatchBadS → MB.MatchBadI → MB.FixIdem → IdemAlg → MatchLMB
def MatchLMGoodOf : Prop := MT.MatchSplit → IdemAlg → MatchLMGood
def MatchLMUnitOf : Prop := MB.MatchUnitI → MT.MatchSplit → IdemAlg → MatchLMUnit

structure MOk (d : LocData E n) : Prop where
  T : ∀ w ∈ d.T, ¬ IsSplitAt w ∧ IsWitt n w (d.b w) ∧ IsUnifAt (d.ϖ w) ∧
    ∀ x ∈ (d.c w).support, StrictAnti x ∧ Cone (lOf x)
  S : ∀ w ∈ d.S₀, IsSplitAt w ∧ (∀ g : GLw n w, g ∈ UL n w) ∧ IsLevel (MonoidHom.id _) (KL n w) ((d.K' w).subgroupOf (UL n w))
  badS : ∀ w ∈ d.Bad, IsSplitAt w → IsLevel (MonoidHom.id _) (KL n w) (d.KB w) ∧
    ∀ (a : ℕ) (ha : a ≤ n), d.fix a w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (U.lone (d.KB w))
  badI : ∀ w ∈ d.Bad, ¬ IsSplitAt w → ∃ k, 1 ≤ k ∧ IsLevel (MonoidHom.id _) (KL n w) (d.KB w) ∧
    (∀ γ : UL n w, γ ∈ d.KB w ↔ γ.1 ∈ MB.congK n w k) ∧
    ∀ a ≤ n, d.fix a w = fun y => (((d.KB w).relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w k y

def MatchLMB2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok → MOk d →
  ∀ (a : ℕ) (ha : a ≤ n) (m : ℕ), ∀ w ∈ d.B,
    Match n a (n - a) w (muAt d w) (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w)

def MatchLMB2Of : Prop := MT.MatchT → MT.MatchLin → MS.MatchSplitPlace → MB.MatchBadS → MB.MatchBadI → MB.FixIdem → IdemAlg → MatchLMB2

end PositivityTheory.Rg.BcB.F.MLM

end

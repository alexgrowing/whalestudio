import Formalism.GaussJetBounds.Statement

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

section TopData

variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)

def WcapOneLetter (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ Dl d TT nu1 size (s - (i : ZMod d))})

def IsLabOneLetter (s s0 : ZMod d) (j : ℤ) : Prop :=
  s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
    (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s)

def JnumOneLetter (s : ZMod d) : ℕ :=
  Set.ncard {q : ZMod d × ℤ | IsLabOneLetter l d TT nu1 size s q.1 q.2}

def kaMaxOneLetter : ℕ := max (TT.sup nu1) (Finset.univ.sup (capL d TT nu1 nu2))

open Classical in

def oddLevelGainSum (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0

end TopData

def digitLossOneLetter {ι : Type v} (l : ℕ) (κ : ι →₀ ℕ) : ℝ :=
  ∑ i ∈ κ.support, ((Nat.log l (κ i) : ℝ) + 1)

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

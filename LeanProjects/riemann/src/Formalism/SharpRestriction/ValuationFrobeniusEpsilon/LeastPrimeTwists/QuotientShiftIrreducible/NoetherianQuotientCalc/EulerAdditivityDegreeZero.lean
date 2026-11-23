import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

def GMod.quots {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] :
    List (Deg k × R) → GMod B R k → GMod B R k
  | [], F => F
  | (_, s) :: ts, F => GMod.quots ts (F.quot s)

def RulePos : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 ts F.Ann → ∀ᶠ m in atTop, 0 ≤ chi ts F m

def RuleUB : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts us : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 (ts ++ us) →
    F.IsGr X.𝒜 → admitted X.𝒜 (ts ++ us) F.Ann →
    ∀ᶠ m in atTop, chi (ts ++ us) F m ≤ chi us (F.quots ts) m

def RuleMono : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F' F F'' : X.Mod), Valid X.𝒜 ts →
    F'.IsGr X.𝒜 → F.IsGr X.𝒜 → F''.IsGr X.𝒜 → SES F' F F'' → admitted X.𝒜 ts F.Ann →
    ∀ᶠ m in atTop, chi ts F'' m ≤ chi ts F m

def RuleSmall : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 [] F.Ann → ∀ᶠ m in atTop,
      chi ts F m = ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
        (-1 : ℤ) ^ I.card * ((Module.length X.B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

def EulerAdditivityDegreeZero : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d : Deg k) (s s' : X.R),
    Valid X.𝒜 ((0, s) :: (d, s') :: ts) → F.IsGr X.𝒜 → admitted X.𝒜 ((d, s * s') :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, s * s') :: ts) F m = chi ((0, s) :: ts) F m + chi ((d, s') :: ts) F m

def RuleCong : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts ts' : List (Deg k × X.R)) (F : X.Mod),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ F.Ann) ts ts' → ∀ m, chi ts F m = chi ts' F m

end Formalism.MainNotions.V.Pf.V2.Calc

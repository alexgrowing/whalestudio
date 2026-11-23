import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition

noncomputable section

namespace Formalism.HC

def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

def maxPrime (Q : ℕ) : ℕ := Q.primeFactors.sup id

def primeChoiceOfBound (Q : ℕ) : ℕ := if Nat.Coprime Q 15 then 3 else nextPrime (maxPrime Q)

def secondPrimeChoiceOfBound (Q : ℕ) : ℕ := if Nat.Coprime Q 15 then 5 else nextPrime (nextPrime (maxPrime Q))

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

def rr : ℕ := primeChoiceOfBound H.QS

def rr' : ℕ := secondPrimeChoiceOfBound H.QS

def radS : ℕ := ∏ l ∈ H.small, l

def bigP : ℕ := ∏ p ∈ (∏ l ∈ H.small, l * (l - 1)).primeFactors.erase 2, p

def vdH (p : ℕ) : ℝ := (padicValNat p (NumberField.discr H.E).natAbs : ℝ) / (Module.finrank ℚ H.E : ℝ)

def vdS : ℝ := ((H.small.sup fun l => padicValNat l (NumberField.discr H.E).natAbs : ℕ) : ℝ) / (Module.finrank ℚ H.E : ℝ)

theorem vdH_nonneg (p : ℕ) : 0 ≤ H.vdH p := by unfold vdH; positivity

end HostRaw

end Formalism.HC

end

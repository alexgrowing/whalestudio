import Formalism.PeriodIntegrals.SqfPrimeFactor
import Formalism.PeriodIntegrals.PrimesDyadicRS

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

def monicDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  Finset.univ.image (fun c : Fin d → ZMod g => X ^ d + ∑ i, C (c i) * X ^ (i : ℕ))

open Classical in

def irrDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (monicDeg g d).filter Irreducible

def bigPrimes (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun p => p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r)

def CountA : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Ev g r f) →
    (T.card : ℝ) ≤ (g : ℝ) ^ r - ∑ p ∈ bigPrimes r, ((irrDeg g p).card : ℝ) * (g : ℝ) ^ (r - p)

def IrrLower : Prop :=
  ∀ (g p : ℕ) [Fact g.Prime], p.Prime → (g : ℝ) ^ p - g ≤ p * ((irrDeg g p).card : ℝ)

def Analytic : Prop :=
  ∀ g r : ℕ, 100 ≤ r → 2 ^ 12 ≤ g →
    (g : ℝ) ^ r - ∑ p ∈ bigPrimes r, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p)
      ≤ (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r

end PI.SqfPrimeFactor.W

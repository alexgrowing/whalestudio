import Formalism.PeriodIntegrals.SqfRootShift

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

def ppSum (N : ℕ) : ℕ := ∑ p ∈ N.primeFactors, p ^ N.factorization p

def CountP : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 3 ≤ g → 1 ≤ r → ∀ (c : (ZMod g)ˣ) (T : Finset (ZMod g)[X]),
    (∀ f ∈ T, Eiii g r c f) →
    (T.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 r, ((ppSum (g ^ k - 1) : ℝ) / k) * (g : ℝ) ^ (r - k)

def ArithP : Prop :=
  ∀ (g r q d e : ℕ), g.Prime → q.Prime → d.Prime → q % 8 = 3 → d % 16 = 7 → 2 ≤ e →
    16 ≤ q → 16 ≤ d → g % (4 * 2 ^ e * q * d) = 1 → 100 ≤ r → 2 ^ 12 ≤ g →
    ∑ k ∈ Finset.Icc 1 r, ((ppSum (g ^ k - 1) : ℝ) / k) * (g : ℝ) ^ (r - k) ≤
      (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log r) / ((g : ℝ) - 1)) * (g : ℝ) ^ r

theorem claim_of (hC : CountP) (hA : ArithP) : PI.SqfRootShift.Claim := by
  intro g r q d e _ hq hd hq8 hd16 he hq16 hd16' hg hr hg12 c T hT
  exact (hC g r (by omega) (by omega) c T hT).trans
    (hA g r q d e Fact.out hq hd hq8 hd16 he hq16 hd16' hg hr hg12)

end PI.SqfRootShift.W

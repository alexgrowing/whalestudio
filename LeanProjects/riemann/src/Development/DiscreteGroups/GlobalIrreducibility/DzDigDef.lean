import Mathlib

namespace DiscreteGroups.sglob.DzType

def Dig : Prop :=
  ∀ (p n : ℕ), p.Prime → 2 ≤ n → 16 * n ^ 2 < p → ∀ k k' : ℕ,
    (∀ i j, i < n → j < n → k * p ^ i ≡ k * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ i j, i < n → j < n → k' * p ^ i ≡ k' * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ u b : ℕ, u.Coprime (p ^ n - 1) →
      (Nat.digits p ((u * k + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k' % (p ^ n - 1))).sum =
        (Nat.digits p ((u * k' + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k % (p ^ n - 1))).sum) →
    ∃ i : ℕ, k' ≡ k * p ^ i [MOD p ^ n - 1]

end DiscreteGroups.sglob.DzType

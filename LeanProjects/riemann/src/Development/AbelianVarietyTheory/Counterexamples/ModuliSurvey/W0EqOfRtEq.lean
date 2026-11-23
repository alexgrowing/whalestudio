import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.HostProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem goodAt_iff (l : Level H) {p : ℕ} (hp : p.Prime) : l.GoodAt p ↔ ∀ k, l.M ≠ p ^ k := by
  have h3 := l.three_le
  have hM : l.M ≠ 0 := by omega
  have hmul : p ^ l.M.factorization p * (l.M / p ^ l.M.factorization p) = l.M :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  unfold Level.GoodAt
  constructor
  · intro h k hk
    rw [hk] at h
    simp [hp.factorization_pow, Nat.div_self (pow_pos hp.pos k)] at h
  · intro h
    set c := l.M / p ^ l.M.factorization p with hc
    have hodd : Odd c := by
      have := l.odd
      rw [← hmul] at this
      exact (Nat.odd_mul.1 this).2
    have h1 : c ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hmul
      exact h _ hmul.symm
    obtain ⟨t, ht⟩ := hodd
    omega

theorem trace_sign (t : ℂ) :
    Algebra.trace ℝ ℂ t = 2 * t.re ∧ Algebra.trace ℝ ℂ (Complex.I * t) = -2 * t.im := by
  simp [Algebra.trace_complex_apply]

end GlobalTheory.HostProbe

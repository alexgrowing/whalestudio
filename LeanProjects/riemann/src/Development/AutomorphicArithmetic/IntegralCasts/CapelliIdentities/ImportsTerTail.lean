import Mathlib

theorem UpperTheory.Reformulated.B.Qf13.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [e]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      calc A.valuation (a ^ n - b ^ n) * A.valuation a
          ≤ A.valuation (a ^ n - b ^ n) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · rw [map_mul, map_pow]
      have hb' : A.valuation b ^ n ≤ 1 := pow_le_one' hb n
      calc A.valuation (a - b) * A.valuation b ^ n
          ≤ A.valuation (a - b) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]

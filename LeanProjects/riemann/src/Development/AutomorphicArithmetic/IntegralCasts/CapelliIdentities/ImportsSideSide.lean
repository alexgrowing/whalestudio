import Mathlib

theorem UpperTheory.Reformulated.B.Ylb4.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k}
      {C : ValuativeRel.ValueGroupWithZero k},
      (∀ (i j : Fin N),
          (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (P i j) ≤
            (1 : ValuativeRel.ValueGroupWithZero k)) →
        (∀ (i j : Fin N),
            (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (Q i j) ≤
              (1 : ValuativeRel.ValueGroupWithZero k)) →
          (∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (B i j) ≤ C) →
            ∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) ((P * B * Q) i j) ≤ C := by
  intro k _ _ N P Q B C hP hQ hB i j
  have hPB : ∀ a b : Fin N, ValuativeRel.valuation k ((P * B) a b) ≤ C := by
    intro a b
    rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro m _
    rw [Valuation.map_mul]
    calc ValuativeRel.valuation k (P a m) * ValuativeRel.valuation k (B m b)
        ≤ 1 * C := mul_le_mul' (hP a m) (hB m b)
      _ = C := one_mul C
  rw [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [Valuation.map_mul]
  calc ValuativeRel.valuation k ((P * B) i l) * ValuativeRel.valuation k (Q l j)
      ≤ C * 1 := mul_le_mul' (hPB i l) (hQ l j)
    _ = C := mul_one C

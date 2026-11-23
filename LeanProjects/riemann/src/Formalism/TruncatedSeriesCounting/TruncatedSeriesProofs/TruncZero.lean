import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul

namespace Formalism.TruncatedSeriesCounting.R9

theorem pow_mem_span_pow_mul : TruncZero := by
  intro R _ u π₀ q ℓ M η y hM hη
  rw [Ideal.mem_span_singleton']
  refine ⟨u ^ y * π₀ ^ (y - M) * q ^ ((ℓ - 1) * y - η), ?_⟩
  have h1 : π₀ ^ y = π₀ ^ (y - M) * π₀ ^ M := by rw [← pow_add, Nat.sub_add_cancel hM]
  have h2 : q ^ ((ℓ - 1) * y) = q ^ ((ℓ - 1) * y - η) * q ^ η := by
    rw [← pow_add, Nat.sub_add_cancel hη]
  rw [mul_pow, mul_pow, ← pow_mul, h1, h2]
  ring

end Formalism.TruncatedSeriesCounting.R9

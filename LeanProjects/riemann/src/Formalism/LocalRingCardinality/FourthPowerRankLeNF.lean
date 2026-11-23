import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

namespace Formalism.BasicNotions

open Formalism.MainNotions

theorem m_pow_four_le_n {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hM : SizeM L) : D.R.m ^ 4 ≤ D.R.n := by
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨-, hMu⟩ := hM
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he : 0 < L.sc.eps := L.sc.eps_pos
  have hd0 : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg hx0.le _
  have hsq : Real.sqrt (L.sc.x * L.sc.delta1) ^ 2 = L.sc.x * L.sc.delta1 :=
    Real.sq_sqrt (mul_nonneg hx0.le hd0)
  have hth : szTh L = L.sc.eps / 100 := rfl
  have e1 : (L.sc.x ^ szTh L) ^ 4 = L.sc.x ^ (szTh L * 4) := by
    rw [Real.rpow_mul hx0.le]
    first
      | (norm_num; done)
      | exact_mod_cast (Real.rpow_natCast (L.sc.x ^ szTh L) 4).symm
  have e2 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = L.sc.x ^ (2 - L.sc.eps / 4) := by
    have h4 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = (L.sc.x * L.sc.delta1) ^ 2 := by
      calc Real.sqrt (L.sc.x * L.sc.delta1) ^ 4
          = (Real.sqrt (L.sc.x * L.sc.delta1) ^ 2) ^ 2 := by ring
        _ = (L.sc.x * L.sc.delta1) ^ 2 := by rw [hsq]
    have h5 : L.sc.x ^ (2 - L.sc.eps / 4)
        = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (-(L.sc.eps / 8) * 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [h4, h5, Real.rpow_mul hx0.le, mul_pow]
    unfold Scale.delta1
    rw [Real.rpow_two, Real.rpow_two]
  have h1 : (D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4 :=
    by
      first
        | exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMu 4
        | gcongr
  have h2 : (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4
      = L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) := by
    rw [mul_pow, e1, e2, ← Real.rpow_add hx0]
  have h3 : L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    rw [hth]
    linarith
  have h6 : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ ((D.R.n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h6

theorem m_pow_four_le_f {D : D7} (L : SizeData₂ D) (h : SizesAt L) : D.R.m ^ 4 ≤ D.R.f := by
  obtain ⟨hN, hM, -⟩ := h
  have h4 := m_pow_four_le_n L hN hM
  show D.R.m ^ 4 ≤ 2 * D.R.n
  first
    | omega
    | linarith

end Formalism.BasicNotions

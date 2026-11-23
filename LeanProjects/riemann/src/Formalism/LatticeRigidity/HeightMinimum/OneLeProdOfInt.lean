import Formalism.LatticeRigidity.StatementD

namespace Formalism.SA.P

open NumberField

section

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E)

end

lemma place_bound (a1 b1 c U U' O G α β : ℝ) (hc : 0 < c)
    (ha : c < a1 ^ 2) (hb : c < b1 ^ 2) (hU0 : 0 ≤ U) (hU'0 : 0 ≤ U')
    (hU : U ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c)) (hU' : U' ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c))
    (hO0 : 0 ≤ O) (hO : O ≤ a1 / (a1 ^ 2 - c) + U * U' * b1 / (b1 ^ 2 - c))
    (hG : 1 ≤ G) (hα : G * O = U' * α) (hβ : G * O = U * β) :
    α * β ≤ 4 * G ^ 2 * (a1 ^ 2 / (a1 ^ 2 - c)) * (b1 ^ 2 / (b1 ^ 2 - c)) / c := by
  have hk1 : 0 < a1 ^ 2 - c := by linarith
  have hk2 : 0 < b1 ^ 2 - c := by linarith
  have hUU : U = U' := (pow_left_inj₀ hU0 hU'0 two_ne_zero).mp (hU.trans hU'.symm)
  subst hUU
  have hr : 0 < U ^ 2 := by rw [hU]; positivity
  have hUpos : 0 < U := by
    rcases hU0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hr; norm_num at hr
  have hO2 : O * (a1 ^ 2 - c) ≤ a1 + b1 := by
    have e : a1 / (a1 ^ 2 - c) + U * U * b1 / (b1 ^ 2 - c) = (a1 + b1) / (a1 ^ 2 - c) := by
      rw [← sq, hU]; field_simp
    rw [e, le_div_iff₀ hk1] at hO
    exact hO
  have hαe : α = G * O / U := by field_simp; linarith
  have hβe : β = G * O / U := by field_simp; linarith
  have hab : α * β = G ^ 2 * O ^ 2 * (a1 ^ 2 - c) / (b1 ^ 2 - c) := by
    rw [hαe, hβe, div_mul_div_comm, ← sq U, hU]
    field_simp
  rw [hab, div_le_div_iff₀ hk2 hc]
  have hkey : c * (a1 + b1) ^ 2 ≤ 4 * a1 ^ 2 * b1 ^ 2 := by nlinarith [sq_nonneg (a1 - b1)]
  have hOk : (O * (a1 ^ 2 - c)) ^ 2 ≤ (a1 + b1) ^ 2 := by
    have : 0 ≤ O * (a1 ^ 2 - c) := by positivity
    exact pow_le_pow_left₀ this hO2 2
  have hG2 : 0 < G ^ 2 := by positivity
  have rhs : 4 * G ^ 2 * (a1 ^ 2 / (a1 ^ 2 - c)) * (b1 ^ 2 / (b1 ^ 2 - c)) * (b1 ^ 2 - c) =
      4 * G ^ 2 * a1 ^ 2 * b1 ^ 2 / (a1 ^ 2 - c) := by
    field_simp
  rw [rhs, le_div_iff₀ hk1]
  calc G ^ 2 * O ^ 2 * (a1 ^ 2 - c) * c * (a1 ^ 2 - c)
      = G ^ 2 * (c * (O * (a1 ^ 2 - c)) ^ 2) := by ring
    _ ≤ G ^ 2 * (4 * a1 ^ 2 * b1 ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left hOk hc.le) hkey) hG2.le
    _ = 4 * G ^ 2 * a1 ^ 2 * b1 ^ 2 := by ring

end Formalism.SA.P

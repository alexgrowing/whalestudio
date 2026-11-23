import Mathlib
import Formalism.PairingDivisors.StatementN

namespace GlobalTheory

theorem legendre_divided_powers : Formalism.PairingDivisionLocalBalance.DivPow := by
  refine ⟨?_, ?_, ?_⟩
  · intro l m hl hl2 hm
    haveI : Fact l.Prime := ⟨hl⟩
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l (n := m) (by omega)
    have hl3 : 3 ≤ l := by
      have := hl.two_le
      omega
    have h2 : 2 * padicValNat l m.factorial ≤ (l - 1) * padicValNat l m.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    constructor <;> omega
  · intro m hm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := padicValNat_factorial_lt_of_ne_zero 2 (n := m) (by omega)
    omega
  · intro j
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, mul_comm, padicValNat_factorial_mul]
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega

end GlobalTheory

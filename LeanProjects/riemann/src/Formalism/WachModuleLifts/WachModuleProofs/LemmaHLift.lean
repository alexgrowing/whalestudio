import Formalism.WachModuleLifts.Statement

namespace Formalism.CL

open Finset

theorem legendreBound : Legendre := by
  unfold Legendre
  intro p hp m
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hq : 0 < q := by have := hp.out.one_lt; omega
  have key : q * padicValNat (q + 1) m.factorial ≤ m := by
    have h := sub_one_mul_padicValNat_factorial (p := q + 1) m
    rw [Nat.add_sub_cancel] at h
    omega
  have hN : (m + padicValNat (q + 1) m.factorial) * q ≤ m * (q + 1) := by nlinarith [key]
  push_cast
  try simp only [add_sub_cancel_right]
  rw [le_div_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast hN

end Formalism.CL

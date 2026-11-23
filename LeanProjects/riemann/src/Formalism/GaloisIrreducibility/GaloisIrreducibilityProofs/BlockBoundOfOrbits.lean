import Formalism.GaloisIrreducibility.NoSolvableOf

namespace Formalism.GaloisIrreducibility

theorem block_bound_of_orbits : BBOf := by
  intro hF g d S hg hd hS hB
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgd : 2 ≤ g ^ d := le_trans hg (Nat.le_self_pow (by omega) g)
  have hn : 1 ≤ g ^ d - 1 := by omega
  have hg1 : (1 : ℝ) < g := by exact_mod_cast hg
  have hpos : (0 : ℝ) < (g : ℝ) ^ ((d : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have key := hF (g ^ d - 1) _ S hn hpos hS hne hB
  have h2 : ((g ^ d - 1 : ℕ) : ℝ) < (g : ℝ) ^ (d : ℝ) := by
    rw [Real.rpow_natCast, Nat.cast_sub (by omega)]; push_cast; linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at key
  have h3 : (d : ℝ) / 4 * S.card < d := (Real.rpow_lt_rpow_left_iff hg1).mp (key.trans h2)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (S.card : ℝ) < 4 := by nlinarith
  have : S.card < 4 := by exact_mod_cast this
  omega

end Formalism.GaloisIrreducibility

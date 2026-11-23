import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_factorial_mul_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) l hp.ne_one
  have hk : k ≤ n := by
    have h1 : k ≤ padicValNat l n.factorial :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    have h2 := sub_one_mul_padicValNat_factorial (p := l) n
    have h3 : 1 ≤ l - 1 := by have := hp.two_le; omega
    have h4 : padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hu : IsUnit ((m : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨u * (l : ℤ_[l]) ^ j, ?_⟩
  rw [h]
  push_cast
  linear_combination ((l : ℤ_[l]) ^ (k + j)) * hu

theorem exists_factorial_mul_eq_pow_ainf (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : Ainf l, ((n.factorial : ℕ) : Ainf l) * c = ((l : ℕ) : Ainf l) ^ n := by
  obtain ⟨c, hc⟩ := exists_factorial_mul_eq_pow l n
  refine ⟨algebraMap ℤ_[l] (Ainf l) c, ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using congrArg (algebraMap ℤ_[l] (Ainf l)) hc

end GlobalTheory.Per

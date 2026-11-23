import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem unitChain_num_sub_half (R : Ranks) (q : ℚ) (hq : ∃ z : ℤ, q = z) (j : ℕ) :
    (((q - (R.N j : ℚ) / 2).num : ℤ) : ℚ) = q - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := hq
  have hN : Even (R.N j) := by
    unfold Ranks.N
    exact R.k_even.add ((R.t_odd.add_one).mul_left j)
  obtain ⟨a, ha⟩ := hN
  have h : (z : ℚ) - (R.N j : ℚ) / 2 = ((z - a : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [h, Rat.num_intCast]

def unitColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) :
    ColumnChain R ι hc where
  cls _ := Unit
  stab _ _ := PUnit
  DGam := 1
  DGam_pos := Nat.one_pos
  dvd_DGam _ _ _ := by simp
  Y _ := Unit
  de _ _ _ := 1
  de_ne _ _ _ := one_ne_zero
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := LinearMap.id
  sSharp i τ := if h : i < R.m then (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sSharp_eq i h τ := by
    rw [dif_pos h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _
  sDiv i τ := if h : i < R.m then (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sDiv_eq i h τ := by
    rw [dif_pos h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _

end GlobalTheory

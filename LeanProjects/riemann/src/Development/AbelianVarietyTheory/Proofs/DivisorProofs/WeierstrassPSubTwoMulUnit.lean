import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPAddSubWeierstrassPSubStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsionStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem eq_of_sq_mul_eq_cube {α : Type*} [LinearOrderedCommGroupWithZero α] {a b c : α} (hc : c ≠ 0)
    (ha : a ≤ c) (hb : b ≤ c) (h : a ^ 2 * b = c ^ 3) : a = c := by
  by_contra hne
  have hlt : a < c := lt_of_le_of_ne ha hne
  have hc0 : 0 < c := zero_lt_iff.mpr hc
  have h1 : a ^ 2 * b ≤ a ^ 2 * c := by gcongr
  have h2 : a ^ 2 < c ^ 2 := pow_lt_pow_left₀ hlt zero_le' two_ne_zero
  have h3 : a ^ 2 * c < c ^ 2 * c := mul_lt_mul_of_pos_right h2 hc0
  have h4 : c ^ 2 * c = c ^ 3 := by rw [pow_succ c 2]
  rw [h4] at h3
  rw [h] at h1
  exact lt_irrefl _ (lt_of_le_of_lt h1 h3)

theorem natCast_mul_intCast_mul_mem (L : PeriodPair) {N : ℕ} {z : ℂ} (hN : (N : ℂ) * z ∈ L.lattice) (k : ℤ) :
    (N : ℂ) * ((k : ℂ) * z) ∈ L.lattice := by
  have e : (N : ℂ) * ((k : ℂ) * z) = k • ((N : ℂ) * z) := by rw [zsmul_eq_mul]; ring
  rw [e]
  exact L.lattice.smul_mem k hN

theorem mem_lattice_of_coprime (L : PeriodPair) {N k : ℕ} (hNk : Nat.Coprime N k) {z : ℂ}
    (hN : (N : ℂ) * z ∈ L.lattice) (hk : (k : ℂ) * z ∈ L.lattice) : z ∈ L.lattice := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hNk
  have hab' : (a : ℂ) * (N : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast hab
  have e : z = a • ((N : ℂ) * z) + b • ((k : ℂ) * z) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-z) * hab'
  rw [e]
  exact L.lattice.add_mem (L.lattice.smul_mem a hN) (L.lattice.smul_mem b hk)

theorem weierstrassP_sub_two_mul_unit : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ¬ 3 ∣ N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → 2 * z ∉ L.lattice ∧ V.valuation (L.weierstrassP z - L.weierstrassP (2 * z)) = V.valuation u ^ 2 := by
  intro L β u V N hβ hβim hu hN hodd h3 z hz hNz
  have cop2 : Nat.Coprime N 2 := (Nat.coprime_two_left.mpr hodd).symm
  have cop3 : Nat.Coprime N 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have h2z : 2 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop2 hNz (by push_cast; exact h))
  have h3z : 3 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop3 hNz (by push_cast; exact h))
  have hN2z : (N : ℂ) * (2 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 2
  have hN3z : (N : ℂ) * (3 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 3
  refine ⟨h2z, ?_⟩
  have e1 : 2 * z - z = z := by ring
  have e2 : 2 * z + z = 3 * z := by ring
  have hd := GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul L (2 * z) z h2z hz (by rw [e1]; exact hz) (by rw [e2]; exact h3z)
  rw [e1, e2] at hd
  have d1 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd z hz hNz
  have d2 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd (2 * z) h2z hN2z
  have m1 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN z (2 * z) hz h2z hNz hN2z).2
  have m2 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN (3 * z) z h3z hz hN3z hNz).2
  have hv : V.valuation u ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hu
    exact latticeCurve_Δ_ne_zero L ((Valuation.zero_iff _).mp hu.symm)
  have hv2 : 0 < V.valuation u ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hv)
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, div_le_one₀ hv2] at m1 m2
  have hval := congrArg V.valuation hd
  rw [map_mul, map_pow, Valuation.map_neg, map_mul, d1, d2,
    Valuation.map_sub_swap V.valuation (L.weierstrassP (2 * z))] at hval
  refine eq_of_sq_mul_eq_cube (pow_ne_zero 2 hv) m1 m2 ?_
  rw [hval, ← pow_add, ← pow_mul]

end GlobalTheory.CMModel

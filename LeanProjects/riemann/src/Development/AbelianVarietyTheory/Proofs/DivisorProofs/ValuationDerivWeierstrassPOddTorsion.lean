import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMulStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem finset_prod_eq_one_of_le_one_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Γ) (hle : ∀ i ∈ s, f i ≤ 1)
    (hprod : ∏ i ∈ s, f i = 1) : ∀ i ∈ s, f i = 1 := by
  intro i hi
  refine le_antisymm (hle i hi) ?_
  rw [← Finset.mul_prod_erase s f hi] at hprod
  have h2 : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one' (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  calc (1 : Γ) = f i * ∏ j ∈ s.erase i, f j := hprod.symm
    _ ≤ f i := mul_le_of_le_one_right' h2

theorem valuation_derivWeierstrassP_torsion_odd :
    ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 →
      V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N →
      ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice →
        V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  intro L β u V N hβ hβim hu hN hodd z hz hNz
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    exact_mod_cast this
  have hstab : MulStable L (N : ℂ) := by
    intro ω hω
    have := L.lattice.smul_mem (N : ℤ) hω
    simpa [zsmul_eq_mul] using this
  have hΔ := latticeCurve_Δ_ne_zero L
  have hvΔ : V.valuation (latticeCurve L).Δ ≠ 0 := by
    simpa using hΔ
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hvΔ
    rw [← hu]; simp
  have hvu : V.valuation u ≠ 0 := by simpa using hu0
  obtain ⟨S, hS⟩ := kerRepsExist L (N : ℂ) hN0 hstab
  have hcard := kerRepsCard L (N : ℂ) S hN0 hstab hS
  have hcardN : S.card + 1 = N * N := by
    have : ((S.card + 1 : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
      push_cast; rw [hcard]; simp [Complex.normSq_apply]
    exact_mod_cast this
  have heven : Even S.card := by
    have hodd2 : Odd (N * N) := hodd.mul hodd
    rw [← hcardN] at hodd2
    obtain ⟨k, hk⟩ := hodd2
    exact ⟨k, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (N : ℂ) S hN0 hstab hS heven
  have hmem : ∀ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ≤ 1 := by
    intro t ht
    rw [ValuationSubring.valuation_le_one_iff]
    exact (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN t t (hS.1 t ht).2 (hS.1 t ht).2 (hS.1 t ht).1
      (hS.1 t ht).1).1
  have hprod : ∏ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ^ 4 = 1 := by
    have hv := congrArg V.valuation hpf
    simp only [map_mul, map_pow, map_prod, hN, one_pow, mul_one] at hv
    simp only [map_div₀, map_pow, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
    rw [hv, ← hu, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hvu)]
    ring_nf
  have hall := finset_prod_eq_one_of_le_one_eq_one S _ (fun t ht => pow_le_one' (hmem t ht) 4) hprod
  obtain ⟨t, ht, hzt⟩ := hS.2.2 z (by simpa [mul_comm] using hNz) hz
  have hper : L.derivWeierstrassP z = L.derivWeierstrassP t := by
    have := L.derivWeierstrassP_add_coe t ⟨z - t, hzt⟩
    simpa using this
  have h1 : V.valuation (L.derivWeierstrassP t / u ^ 3) = 1 := by
    have h4 := hall t ht
    by_contra hne
    have hlt : V.valuation (L.derivWeierstrassP t / u ^ 3) < 1 := lt_of_le_of_ne (hmem t ht) hne
    exact absurd h4 (ne_of_lt (pow_lt_one' hlt (by norm_num)))
  rw [hper]
  rw [map_div₀, map_pow, div_eq_one_iff_eq (pow_ne_zero _ hvu)] at h1
  exact h1
end GlobalTheory

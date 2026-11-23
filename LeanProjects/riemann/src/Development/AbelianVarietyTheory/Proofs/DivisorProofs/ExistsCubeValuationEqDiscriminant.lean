import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisStableTorsionFamilyKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPSubTwoMulUnitStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_mem_valuation_cube_eq_Δ : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ,
      ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  intro p F L t hp h4 h3 hD V
  obtain ⟨N, ι, _, T, hNodd, hN3, hNv, hcard, hst, hT⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp h4 h3 hD V
  have hΔ0 := latticeCurve_Δ_ne_zero L
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (by norm_num : 0 < 12)
  have hu0 : u ≠ 0 := by rintro rfl; exact hΔ0 (by rw [← hu]; simp)
  have hvu : V.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hvΔ : V.valuation (latticeCurve L).Δ = V.valuation u ^ 12 := by rw [← hu, map_pow]
  have hβ : (sqrtNegNat p).im ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp [sqrtNegNat, Real.sqrt_ne_zero'.2 this]
  have hN3' : ¬ 3 ∣ N := by omega
  have hU := fun i => GlobalTheory.T.valuation_weierstrassP_sub_two_mul_eq_sq L (sqrtNegNat p) u V N hD.mul hβ hvΔ.symm hNv hNodd hN3' (T i)
    (hT i).1 (hT i).2
  have hmem := (GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hD.g₂_mem hD.g₃_mem hst (fun i => (hT i).1)).2.2.2
    (fun i => (hU i).1)
  have hΔmem : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3)
      (mul_mem (by simpa using natCast_mem F 27) (pow_mem hD.g₃_mem 2))
  set U := ∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i)) with hUdef
  obtain ⟨n, hn⟩ : ∃ n, N = 3 * n + 2 := ⟨N / 3, by omega⟩
  have hvU : V.valuation U = V.valuation u ^ (12 * n) * V.valuation u ^ 4 := by
    rw [hUdef, map_prod]
    simp_rw [fun i => (hU i).2]
    rw [Finset.prod_const, Finset.card_univ, hcard, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hU0 : U ≠ 0 := by
    intro h
    rw [h, map_zero] at hvU
    exact (mul_ne_zero (pow_ne_zero _ hvu) (pow_ne_zero _ hvu)) hvU.symm
  refine ⟨U / (latticeCurve L).Δ ^ n, div_mem hmem (pow_mem hΔmem n),
    div_ne_zero hU0 (pow_ne_zero _ hΔ0), ?_⟩
  rw [map_div₀, map_pow, hvU, hvΔ, ← pow_mul, mul_comm 12 n, mul_div_cancel_left₀ _ (pow_ne_zero _ hvu),
    ← pow_mul]

end GlobalTheory.CMModel

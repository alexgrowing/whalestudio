import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassCoeffsIntegralAverageChangeOfVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntVVariableChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordsMemOfOddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsionStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.modelAt_of_stable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro L β u V N hβ hβim hu12 hN hNodd F ι _ T hg2 hg3 huF hst hT hcard
  have hΔ := latticeCurve_Δ_ne_zero L
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (by norm_num)] at hu12
    exact hΔ ((Valuation.zero_iff _).mp hu12.symm)
  have hj : (latticeCurve L).j ∈ V := by
    have hi : _root_.IsIntegral V (latticeCurve L).j := (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L β hβ hβim).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    rw [← hy]; exact y.2
  obtain ⟨r, s, t, hint⟩ := GlobalTheory.T.exists_variableChange_intV_of_j_mem (latticeCurve L) V (Units.mk0 u hu) hj hu12
  have htm := fun i => GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV L β u V N hβ hβim hu12 hN hNodd hu r s t hint (T i) (hT i).1 (hT i).2
  have hud := fun i => GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu12 hN hNodd (T i) (hT i).1 (hT i).2
  have havg := GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables V (-L.g₂ / 4) (-L.g₃ / 4) r s t (Units.mk0 u hu) ι
    (fun i => L.weierstrassP (T i)) (fun i => L.derivWeierstrassP (T i) / 2) hint hcard
    (fun i => (htm i).1) (fun i => (htm i).2)
    (fun i => by
      show V.valuation (2 * (L.derivWeierstrassP (T i) / 2)) = V.valuation u ^ 3
      rw [mul_div_cancel₀ _ two_ne_zero]; exact hud i)
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hg2 hg3 hst (fun i => (hT i).1)
  have hnF : ((Fintype.card ι : ℕ) : ℂ) ∈ F := natCast_mem F _
  refine ⟨⟨Units.mk0 u hu, (∑ i, L.weierstrassP (T i)) / Fintype.card ι,
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) / Fintype.card ι,
    (∑ i, L.derivWeierstrassP (T i) / 2) / Fintype.card ι⟩, huF, div_mem h1 hnF, div_mem h3 hnF,
    div_mem h2 hnF, havg, ?_⟩
  have hv : V.valuation u ^ 12 ≠ 0 := by
    rw [hu12]; exact (Valuation.ne_zero_iff _).mpr hΔ
  rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, map_one,
    ← hu12, inv_pow, inv_mul_cancel₀ hv]

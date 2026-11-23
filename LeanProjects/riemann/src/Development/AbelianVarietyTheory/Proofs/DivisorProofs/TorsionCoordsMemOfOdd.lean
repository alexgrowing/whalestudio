import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfDuplicationEqStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem torsion_coords_mem_of_odd : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  intro L β u V N hmul hβ hΔ hN hodd hu r s t hint z hz hNz
  have h2z : 2 * z ∉ L.lattice := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    have e : z = (N : ℂ) * z - ((k : ℤ) • (2 * z)) := by
      rw [zsmul_eq_mul, hk]; push_cast; ring
    exact hz (e ▸ sub_mem hNz (L.lattice.smul_mem _ h))
  have hNz2 : (N : ℂ) * (2 * z) ∈ L.lattice := by
    have e : (N : ℂ) * (2 * z) = N * z + N * z := by ring
    rw [e]; exact add_mem hNz hNz
  obtain ⟨hP', -⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN z z hz hz hNz hNz
  obtain ⟨-, hδ⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN (2 * z) z h2z hz hNz2 hNz
  have dup := GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq L z hz h2z
  have sq := L.derivWeierstrassP_sq z hz
  set C : VariableChange ℂ := ⟨Units.mk0 u hu, r, s, t⟩ with hC
  have hCu : ((C.u⁻¹ : ℂˣ) : ℂ) = u⁻¹ := by simp [hC]
  have hCr : C.r = r := rfl
  have hCs : C.s = s := rfl
  have hCt : C.t = t := rfl
  set P := L.weierstrassP z with hPdef
  set P' := L.derivWeierstrassP z with hP'def
  set P2 := L.weierstrassP (2 * z) with hP2def
  have hD : 2 * ((P' / 2 - t - s * (P - r)) / u ^ 3) + (C • latticeCurve L).a₁ * ((P - r) / u ^ 2)
      + (C • latticeCurve L).a₃ = P' / u ^ 3 := by
    rw [variableChange_a₁, variableChange_a₃, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    field_simp
    ring
  apply GlobalTheory.T.mem_of_duplication_eq_weierstrass V (C • latticeCurve L) _ _ ((P2 - P) / u ^ 2) hint
  · rw [Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine]
    rw [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    linear_combination (norm := skip) (1 / 4 * u⁻¹ ^ 6) * sq
    field_simp
    ring
  · rw [hD]; exact hP'
  · exact hδ
  · rw [hD, variableChange_b₄, variableChange_b₆, variableChange_b₈, hCu, hCr]
    simp only [latticeCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (norm := skip) (u⁻¹ ^ 8) * (-dup + (2 * P + r) * sq)
    field_simp
    ring

end GlobalTheory.CMModel

import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.tangentSlope_mem : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t X Y : ℂ) (u : ℂˣ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → (X - r) / (u : ℂ) ^ 2 ∈ V → (Y - t - s * (X - r)) / (u : ℂ) ^ 3 ∈ V → V.valuation (2 * Y) = V.valuation (u : ℂ) ^ 3 → ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) ∈ V := by
  intro V a₄ a₆ r s t X Y u hI hx hy hv
  obtain ⟨h1, h2, -, h4, -⟩ := hI
  set W' := (⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ) with hW'
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hY : 2 * Y ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact pow_ne_zero 3 ((Valuation.ne_zero_iff _).2 hu) hv.symm
  have hY0 : Y ≠ 0 := right_ne_zero_of_mul hY
  have hq : (u : ℂ) ^ 3 / (2 * Y) ∈ V := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, ← hv, div_self]
    exact (Valuation.ne_zero_iff _).2 hY
  have hE : 3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3) ∈ V := by
    have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
    have h2' : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
    exact sub_mem (add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' h2) hx)) h4)
      (mul_mem h1 hy)
  have key : ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) =
      (3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3)) * ((u : ℂ) ^ 3 / (2 * Y)) := by
    simp only [hW', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [key]
  exact mul_mem hE hq

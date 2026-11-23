import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvNatSmulMemDiscreteSubmodule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_inv_nat_smul_mem_discrete_submodule : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  first | exact @GlobalTheory.discrete_submodule_inv_smul_eq_zero | exact GlobalTheory.discrete_submodule_inv_smul_eq_zero | (intros; apply GlobalTheory.discrete_submodule_inv_smul_eq_zero <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory

theorem discrete_submodule_inv_smul_eq_zero : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  intro g Λ hΛ d hd
  have hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0) := by
    simpa using hc1.smul_const d
  let f : ℕ → Λ := fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [tendsto_subtype_rng]
    simpa [f] using hlim
  rw [nhds_discrete, Filter.tendsto_pure] at hf
  obtain ⟨k, hk⟩ := hf.exists
  have h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0 := congrArg Subtype.val hk
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exfalso
    rw [inv_eq_zero] at h0
    exact (Nat.cast_ne_zero.mpr k.succ_ne_zero) h0
  · exact h0

end GlobalTheory

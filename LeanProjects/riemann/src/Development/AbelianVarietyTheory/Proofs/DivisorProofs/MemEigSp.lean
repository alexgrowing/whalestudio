import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

def eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) where
  carrier := {u | ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u}
  add_mem' := by
    intro u v hu hv c
    rw [Matrix.mulVec_add, hu c, hv c, smul_add]
  zero_mem' := by intro c; simp
  smul_mem' := by
    intro a u hu c
    rw [Matrix.mulVec_smul, hu c, smul_comm]

theorem mem_eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ)
    (u : Fin g → ℂ) : u ∈ eigSp φ τ ↔ ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u := Iff.rfl

end GlobalTheory.UPel.HT.LieType

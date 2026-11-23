import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem fracId_exists_totPos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F),
    ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  intro F _ _ _ 𝔠
  have hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h
    apply 𝔠.ne_zero
    exact (FractionalIdeal.coeToSubmodule_eq_bot).mp h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 := by
    rw [hy, Algebra.smul_def]
    exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0
  refine ⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  intro τ
  have hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y := by
    rw [mul_comm a y, mul_smul, ← hy, Algebra.smul_def]
  show 0 < τ ((a * y) • x)
  rw [hval, map_mul]
  have : τ (algebraMap (𝓞 F) F y) ≠ 0 := (map_ne_zero τ).mpr hy0
  exact mul_self_pos.mpr this

end GlobalTheory.RealMult

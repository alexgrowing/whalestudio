import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal

open NumberField ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM

namespace GlobalTheory.LamF

theorem deg_eq_ndeg_of_line : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (ℓ : MLine K),
    v ≠ 0 → ℓ.Good → (∀ z, z ∈ Λ ↔ ∃ c ∈ ℓ.I, z = c • v) → (∀ s, ℓ.n s ^ 2 = (h.form s v v).re) →
    deg h Λ = ℓ.ndeg := by
  intro K _ _ V _ _ _ _ h Λ v ℓ hv hℓ hΛ hn
  rw [GlobalTheory.CM.deg_ideal_smul h Λ hv (m := fun s => ℓ.n s ^ 2) (fun s => pow_pos (hℓ.2 s) 2)
    (fun s => (hn s).symm) hℓ.1 (fun z => (hΛ z).trans ⟨fun ⟨c, a, b⟩ => ⟨c, b, a⟩, fun ⟨c, a, b⟩ => ⟨c, b, a⟩⟩),
    MLine.ndeg, MLine.deg, meanLog]
  simp only [Real.log_pow, ← Finset.mul_sum, Nat.cast_ofNat]
  ring

end GlobalTheory.LamF

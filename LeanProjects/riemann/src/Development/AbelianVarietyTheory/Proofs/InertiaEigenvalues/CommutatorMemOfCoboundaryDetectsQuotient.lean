import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegerCoboundaryAdditiveModPrimePow
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem commutator_mem_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hdet σ hσ τ hτ
  by_contra hc
  have hcA : σ * τ * σ⁻¹ * τ⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) (A.inv_mem hτ)
  obtain ⟨x, a, hx, hnd⟩ := hdet _ hcA hc
  have hadd := GlobalTheory.PMon.Ram.coboundary_int_additive_mod K L p E r A x a hp hE hord hx
  have h1 : (p : ℤ) ^ r ∣ a 1 := by
    have := hadd 1 A.one_mem 1 A.one_mem
    simp only [mul_one] at this
    have h' : a 1 = -(a 1 - a 1 - a 1) := by ring
    rw [h']; exact this.neg_right
  have hinv : ∀ g ∈ A, (p : ℤ) ^ r ∣ a g⁻¹ + a g := by
    intro g hg
    have := hadd g⁻¹ (A.inv_mem hg) g hg
    rw [inv_mul_cancel] at this
    have h' : a g⁻¹ + a g = a 1 - (a 1 - a g⁻¹ - a g) := by ring
    rw [h']; exact dvd_sub h1 this
  have e1 := hadd (σ * τ * σ⁻¹) (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) τ⁻¹ (A.inv_mem hτ)
  have e2 := hadd (σ * τ) (A.mul_mem hσ hτ) σ⁻¹ (A.inv_mem hσ)
  have e3 := hadd σ hσ τ hτ
  have e4 := hinv σ hσ
  have e5 := hinv τ hτ
  apply hnd
  have h' : a (σ * τ * σ⁻¹ * τ⁻¹) =
      (a (σ * τ * σ⁻¹ * τ⁻¹) - a (σ * τ * σ⁻¹) - a τ⁻¹) + (a (σ * τ * σ⁻¹) - a (σ * τ) - a σ⁻¹)
        + (a (σ * τ) - a σ - a τ) + (a σ⁻¹ + a σ) + (a τ⁻¹ + a τ) := by ring
  rw [h']
  exact dvd_add (dvd_add (dvd_add (dvd_add e1 e2) e3) e4) e5

end GlobalTheory.PMon.Ram

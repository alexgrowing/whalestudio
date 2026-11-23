import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

def UniqInv : Prop :=
  ∀ Λ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0 → Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ' →
    Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ' → Λ = Λ'

def LatOfDiscr : Prop :=
  ∀ Λ : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0 → IsLat Λ

def ExtendEmb : Prop :=
  ∀ (M : IntermediateField ℚ ℂ), Algebra.IsAlgebraic ℚ M → ∀ ρ : M →ₐ[ℚ] ℂ,
    ∃ σ : ℂ ≃+* ℂ, ∀ x : M, σ (x : ℂ) = ρ x

def CMConjSet (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ (M : IntermediateField ℚ ℂ) [NumberField M]
    (h : jL (lamOf D cc 1) ∈ M),
    (∀ ρ : M →ₐ[ℚ] ℂ, ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ ρ ⟨jL (lamOf D cc 1), h⟩ = jL (lamOf D 𝔟 1)) ∧
    ∀ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ →
      ((Finset.univ.filter fun ρ : M →ₐ[ℚ] ℂ => ρ ⟨jL (lamOf D cc 1), h⟩ = jL (lamOf D 𝔟 1)).card : ℝ) *
        (Fintype.card (ClassGroup (𝓞 D.host.K)) : ℝ) = (Module.finrank ℚ M : ℝ)

def CMConjSetF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    ∀ x : K, x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → ∀ φ : K →+* ℂ,
    ∀ cc : Ideal (𝓞 K), cc ≠ ⊥ → ∀ (M : IntermediateField ℚ ℂ) [NumberField M]
    (h : jL (latI φ cc 1) ∈ M),
    (∀ ρ : M →ₐ[ℚ] ℂ, ∃ 𝔟 : Ideal (𝓞 K), 𝔟 ≠ ⊥ ∧ ρ ⟨jL (latI φ cc 1), h⟩ = jL (latI φ 𝔟 1)) ∧
    ∀ 𝔟 : Ideal (𝓞 K), 𝔟 ≠ ⊥ →
      ((Finset.univ.filter fun ρ : M →ₐ[ℚ] ℂ => ρ ⟨jL (latI φ cc 1), h⟩ = jL (latI φ 𝔟 1)).card : ℝ) *
        (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = (Module.finrank ℚ M : ℝ)

theorem uniqInv_of_lat (hL : LatOfDiscr) (hU : Uniformization) : UniqInv := by
  intro Λ Λ' hd h2 h3
  have hd0 : Formalism.MainNotions.TaylorLogMetric.g2 Λ ^ 3 - 27 * Formalism.MainNotions.TaylorLogMetric.g3 Λ ^ 2 ≠ 0 := hd
  have hd' : Formalism.MainNotions.TaylorLogMetric.discr Λ' ≠ 0 := by
    unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [← h2, ← h3]
    exact hd0
  exact (hU _ _ hd0).2 Λ Λ' (hL Λ hd) (hL Λ' hd') rfl rfl h2.symm h3.symm

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end

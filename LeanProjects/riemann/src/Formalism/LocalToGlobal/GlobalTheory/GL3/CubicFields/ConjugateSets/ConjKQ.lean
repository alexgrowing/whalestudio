import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

def jI (d : ℕ) (𝔞 : Ideal (𝓞 (KQ d))) : ℂ := jL (latI (algebraMap (KQ d) ℂ) 𝔞 1)

def JSet (d : ℕ) : Set ℂ := {y | ∃ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ ∧ y = jI d 𝔟}

def ConjKQ (d : ℕ) : Prop :=
  ∀ cc : Ideal (𝓞 (KQ d)), cc ≠ ⊥ → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (h : jI d cc ∈ M),
    (∀ ρ : M →ₐ[ℚ] ℂ, ∃ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ ∧ ρ ⟨jI d cc, h⟩ = jI d 𝔟) ∧
    ∀ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ →
      ((Finset.univ.filter fun ρ : M →ₐ[ℚ] ℂ => ρ ⟨jI d cc, h⟩ = jI d 𝔟).card : ℝ) *
        (Fintype.card (ClassGroup (𝓞 (KQ d))) : ℝ) = (Module.finrank ℚ M : ℝ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end

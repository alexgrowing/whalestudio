import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.global_euler_char_rat_of_ne_two :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), ContainsAbove S l →
          ∀ ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M, ContAction ρ → ∀ σ : G ℚ Ω, (∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x)) →
          Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          Module.finrank k (H0 ρ) + Module.finrank k (H2 ρ) + Module.finrank k M = Module.finrank k (H1 ρ) + Module.finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) := by
  intro hf he Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ hl S hS ρ hρ σ hσ
  haveI : Finite M := Module.finite_of_finite k
  have hcc : IsCC σ := hσ
  obtain ⟨h1, h2, h3⟩ := UpperTheory.global_euler_characteristic_rationals_odd_prime hf he Ω l hl k M S ρ hS hρ σ hcc
  exact ⟨h1, h2, h3.symm⟩

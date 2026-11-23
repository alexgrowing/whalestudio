import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegularStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplexStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem top_le_preimage_of_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : Sp ℂ) (U : X.Opens)
    (hp : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  obtain rfl : q = p := Subsingleton.elim q p
  exact hp

theorem algebraic_coboundary_of_holomorphic_coboundary : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i, ∃ a : Γ(P₀.A.left, O i), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → valAt' (u.ex z).left (O i) a = h i z := by
  intro hL P₀ u Hm χ hU I O c h hcov hhol hcoc i

  refine (GlobalTheory.T.existsUnique_section_of_locally_given_values P₀ u Hm χ hU (O i) (h i) ?_).exists
  intro z hz
  obtain ⟨p⟩ : Nonempty (Sp ℂ) := inferInstance
  have hy : (u.ex z).left p ∈ O i := hz (Set.mem_univ p)
  obtain ⟨n, σ, hyσ, hσ⟩ := GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex hL P₀ (O i) _ hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_regular_on_section_nonzeroLocus P₀ u Hm χ hU I O c h hcov hhol hcoc i n σ hσ
  exact ⟨Out.nonzeroLocus σ, a, hσ, top_le_preimage_of_mem _ p _ hyσ, ha⟩

end GlobalTheory.KS

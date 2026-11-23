import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomInjectiveApplyOfTranscendental
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algHom_algebraicClosure_apply_eq_pow :
    ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m →
      ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  intro Ω _ K0 x hx m hm
  classical
  have h1 : AlgebraicIndepOn K0 id ({x} : Set Ω) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let i₀ : s := ⟨x, hxs rfl⟩
  have h2 := (algebraicIndependent_update_pow hs.1 i₀ hm).map'
    (f := IsScalarTower.toAlgHom K0 Ω (AlgebraicClosure Ω))
    (algebraMap Ω (AlgebraicClosure Ω)).injective
  obtain ⟨j, hj⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hs h2
  exact ⟨j, by simpa [i₀] using hj i₀⟩

end GlobalTheory

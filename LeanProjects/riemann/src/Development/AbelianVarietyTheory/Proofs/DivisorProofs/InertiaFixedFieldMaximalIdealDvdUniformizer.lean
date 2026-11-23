import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedPosValuationDvdUniformiserStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FixInertUnram

theorem mem_nonunits_iff' {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← A.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ ((Valuation.pos_iff _).2 hx)]
    simp [hx]

theorem div_uniformizer_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ∈ V.nonunits →
      x / algebraMap K Ω (algebraMap R K π) ∈ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx hxV
  let L : IntermediateField K Ω :=
    (FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)).toIntermediateField
  have hxL : x ∈ L := FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  let W : ValuationSubring L := V.comap (algebraMap L Ω)
  have hW : IsAbove R K W.toSubring := by
    unfold IsAbove at hV ⊢
    rw [← hV]
    ext y
    rfl
  let y : L := ⟨x, hxL⟩
  have hfix : ∀ τ ∈ inertia K W, τ y = y := by
    intro τ hτ
    obtain ⟨σ, hσ, he⟩ := GlobalTheory.T.exists_inertia_element_restricting_to_finite_galois R K Ω V hV L τ hτ
    apply Subtype.ext
    rw [← he y]
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσ
  have hyW : y ∈ W.nonunits := by
    rw [mem_nonunits_iff'] at hxV ⊢
    rcases hxV with h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr fun h' => h ?_
      have : ((y⁻¹ : L) : Ω) ∈ V := h'
      simpa using this
  have key := GlobalTheory.T.inertia_fixed_pos_valuation_dvd_uniformiser R K L W hW π hπ y hfix hyW
  have : ((y / algebraMap K L (algebraMap R K π) : L) : Ω) ∈ V := key
  simpa using this

end GlobalTheory.FixInertUnram

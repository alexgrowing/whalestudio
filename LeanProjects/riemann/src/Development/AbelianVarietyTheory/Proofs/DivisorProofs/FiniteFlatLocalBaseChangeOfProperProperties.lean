import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem finiteFlat_proper_baseChange_facts : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  intro R R' _ _ _ _ ρ hinj hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  have h1 : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin
  have h2 : IsFinite k := MorphismProperty.of_isPullback (P := @IsFinite) hk.flip h1
  have h3 : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hk' hp
  have h4 : Surjective (spMap ρ) :=
    ⟨RingHom.IsIntegral.comap_surjective hfin.to_isIntegral hinj⟩
  have h5 : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hk.flip h4
  have h6 : Surjective k' := MorphismProperty.of_isPullback (P := @Surjective) hk'.flip h5
  refine ⟨h2, inferInstance, inferInstance, h6.surj, (p' ≫ k).isClosedMap, p.isClosedMap, ?_, ?_⟩
  · intro V hV
    refine ⟨QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact, ?_⟩
    haveI : IsAffine V := hV
    haveI : QuasiSeparatedSpace (p ⁻¹ᵁ V : Z.Opens).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (p ∣_ V)
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (p ⁻¹ᵁ V).isOpen).mpr this
  · letI := ρ.toAlgebra
    haveI : Module.Finite R R' := hfin
    haveI : Module.Flat R R' := hflat
    haveI : Module.Free R R' := Module.free_of_flat_of_isLocalRing
    let b := Module.finBasis R R'
    refine ⟨_, b, fun r' => ⟨b.repr r', ?_, ?_⟩⟩
    · exact (b.sum_repr r').symm
    · intro c hc
      have : r' = ∑ l, c l • b l := hc
      rw [this, b.repr_sum_self]

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvUnit

theorem exists_unit_of_mem_range {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (u : Bˣ) (h : u.val ∈ Set.range f) (h' : (u⁻¹).val ∈ Set.range f) : ∃ g : Aˣ, Units.map (f : A →* B) g = u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  have e : g * g' = 1 := hf (by rw [map_mul, hg, hg', map_one, Units.mul_inv])
  exact ⟨⟨g, g', e, (mul_comm g' g).trans e⟩, Units.ext hg⟩

theorem map_inv_eq {B : Type} [CommRing B] (t : B →+* B) (u : Bˣ) (h : t u.val = u.val) :
    t (u⁻¹).val = (u⁻¹).val := by
  have e : u.val * t (u⁻¹).val = 1 := by
    conv_lhs => rw [← h]
    rw [← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem invariant_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  intro R _ _ _ _ R' _ _ _ ρ hF hG G' _ G _ _ β act hS hβ hact hinv O
  have := hS.smooth
  have H := GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hF hG G.left G'.left G.hom G'.hom β inferInstance hβ.1 act hinv
    (fun σ => (hact σ).1.w) O
  refine ⟨H.1, fun u hu => ?_⟩
  exact exists_unit_of_mem_range (β.app O).hom H.1 u (H.2 _ hu) (H.2 _ fun σ h => map_inv_eq _ u (hu σ h))

end GlobalTheory.Mum.InvUnit

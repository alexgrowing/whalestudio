import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_isReduced_isNormal_flat :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X → IsReduced X') ∧ (IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') ∧ ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (s' : X' ⟶ Sp R), Flat (π ≫ s') → Flat s' := by
  rintro Γ _ _ X X' ρ π ⟨_, hπ, hV⟩
  have h : IsAffineQuotient ρ π :=
    ⟨hπ, ‹_›, fun W ↦ (hV W).1, fun W s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2⟩
  refine ⟨fun _ ↦ h.isReduced, fun _ hN ↦ ?_, fun R _ _ s' _ ↦ ?_⟩
  · have := IsNormalScheme.of_pred hN
    have := h.isNormalScheme
    exact IsNormalScheme.pred X'
  · have := h.isSchemeTheoreticallyDominant
    exact flat_of_isSchemeTheoreticallyDominant
      (fun _ _ _ h ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr h) π s'

end GlobalTheory

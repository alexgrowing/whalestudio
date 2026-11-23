import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 4).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr

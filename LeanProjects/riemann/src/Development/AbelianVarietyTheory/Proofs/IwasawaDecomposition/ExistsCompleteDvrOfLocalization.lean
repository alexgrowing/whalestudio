import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.PrimeTrait

theorem exists_cdvr_of_localization_atPrime :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (Q : Ideal R) [Q.IsPrime], IsDiscreteValuationRing (Localization.AtPrime Q) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ϖ : W) (g : R →+* W), CDvr W ∧ Irreducible ϖ ∧ Function.Injective g ∧ (∀ r, r ∉ Q → IsUnit (g r)) ∧ ∃ π ∈ Q, Associated (g π) ϖ := by
  intro R _ _ _ Q _ hV
  set V := Localization.AtPrime Q
  have hRV : Function.Injective (algebraMap R V) :=
    IsLocalization.injective V Q.primeCompl_le_nonZeroDivisors
  haveI : CharZero V := charZero_of_injective_algebraMap hRV
  haveI : IsDomain V := inferInstance
  set W := AdicCompletion (maximalIdeal V) V
  have hVW : Function.Injective (algebraMap V W) := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero W := charZero_of_injective_algebraMap hVW
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective Q.primeCompl p
  have hs : IsUnit (algebraMap R V s) := IsLocalization.map_units V s
  have hap : algebraMap R V a = p * algebraMap R V s := by
    rw [← has]; exact (IsLocalization.mk'_spec V a s).symm
  have haQ : a ∈ Q := by
    by_contra ha
    have hu : IsUnit (algebraMap R V a) := IsLocalization.map_units V (⟨a, ha⟩ : Q.primeCompl)
    rw [hap] at hu
    exact hp.not_isUnit (isUnit_of_mul_isUnit_left hu)
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W p,
    (algebraMap V W).comp (algebraMap R V), ?_, GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hp,
    hVW.comp hRV, ?_, a, haQ, ?_⟩
  · exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro r hr
    exact (IsLocalization.map_units V (⟨r, hr⟩ : Q.primeCompl)).map (algebraMap V W)
  · refine Associated.symm ⟨(hs.map (algebraMap V W)).unit, ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, IsUnit.unit_spec, hap, map_mul]

end GlobalTheory.PrimeTrait

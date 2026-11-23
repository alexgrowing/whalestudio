import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.LocalFourierHaar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.Uniformiser

theorem valued_eq_exp_neg_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (h1 : a ∈ v.asIdeal) (h2 : a ∉ v.asIdeal ^ 2) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-1 : ℤ) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  rw [show algebraMap F (v.adicCompletion F) (a : F) = ((a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : v.intValuation a ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem v a 1).2 (by simpa using h1)
  have hnle2 : ¬ v.intValuation a ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v a 2).1 h)
  have hne : v.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v a ha0
  rw [← WithZero.exp_log hne] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  omega

theorem ord_eq_zero_of_valued_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    GroundTheory.LocalField.ord x = 0 := by
  have heq : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion F)) := ValuativeRel.isEquiv _ _
  have h1 : ValuativeRel.valuation (v.adicCompletion F) x = 1 := heq.eq_one_iff_eq_one.1 hx
  unfold GroundTheory.LocalField.ord
  rw [GroundTheory.LocalField.normalizedValuation_apply, h1, map_one, WithZero.log_one, neg_zero]

theorem ord_ratio_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 →
    ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) →
    GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  intro F _ _ v ϖ ϖ' h1 h2 h1' h2' U hU
  apply ord_eq_zero_of_valued_eq_one v
  have e1 := valued_eq_exp_neg_one v ϖ h1 h2
  have e2 := valued_eq_exp_neg_one v ϖ' h1' h2'
  have h := congrArg Valued.v hU
  rw [map_mul, e1, e2] at h
  exact mul_right_cancel₀ WithZero.exp_ne_zero (h.trans (one_mul _).symm)

end GlobalTheory.CompanionTheory.Uniformiser

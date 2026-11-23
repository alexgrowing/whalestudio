import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLinkMono

theorem mul_rpow_self_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') (h0 : 0 ≤ C') :
    C * x ^ C ≤ C' * x ^ C' := by
  have hxp : 0 < x := lt_of_lt_of_le one_pos hx
  rcases le_or_gt 0 C with hC | hC
  · exact mul_le_mul h (Real.rpow_le_rpow_of_exponent_le hx h) (Real.rpow_nonneg hxp.le _) h0
  · have : C * x ^ C ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hxp.le _)
    exact this.trans (mul_nonneg h0 (Real.rpow_nonneg hxp.le _))

theorem rpow_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') : x ^ C ≤ x ^ C' :=
  Real.rpow_le_rpow_of_exponent_le hx h

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  intro D L P X C C' h h0
  have hx : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hxp : 0 < L.sc.x := lt_of_lt_of_le one_pos hx
  have hCx := mul_rpow_self_mono hx h h0
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hxp.le _
  have he : 0 ≤ L.etaSz := L.etaSz_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨tf, hF, hB⟩
    refine ⟨tf, ?_, hB⟩
    intro i hi hl
    refine (hF i hi hl).trans ?_
    have h1 : C * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x ≤
        C' * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by
      have hk : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by positivity
      have := mul_le_mul_of_nonneg_right h hk
      simpa only [mul_assoc] using this
    have h2 : C * L.sc.x ^ C * TwistedPlaces.large₂ L ^ 2 ≤ C' * L.sc.x ^ C' * TwistedPlaces.large₂ L ^ 2 :=
      mul_le_mul_of_nonneg_right hCx (sq_nonneg _)
    linarith
  · intro hH j hj l hl
    refine (hH j hj l hl).trans ?_
    have hk : 0 ≤ Real.log l * (L.dZ0 j : ℝ) :=
      mul_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hk
    have := mul_le_mul_of_nonneg_right hCx he
    linarith
  · intro hB i hi hg hr π hπ
    refine (hB i hi hg hr π hπ).trans ?_
    have hk : 0 ≤ (D.R.f : ℝ) * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h hk
    simpa only [mul_assoc] using this
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hr := rpow_mono hx h
    refine ⟨h1.trans h, h2.trans h, h3.trans hr, h4.trans hr, h5.trans hr, h6, h7.trans hCx, h8.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCx hLg

end GlobalTheory.NLinkMono

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRatio

theorem ratio_cong : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ v A hA u hu π t hπ ht τ τ' _hτ hτ' h1 h2
  have hq1 : 1 < normV v := by
    unfold normV
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have : Finite (𝓞 E ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    exact Finite.one_lt_card
  set U : Ω := algebraMap E Ω (u : E) with hUdef
  have hint : IsIntegral ℤ U := (RingOfIntegers.isIntegral_coe u).map ((algebraMap E Ω).toIntAlgHom)
  have hUle : A.valuation U ≤ 1 :=
    (Valuation.valuationSubring.integers A.valuation).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top hint)
  have hU1 : A.valuation U = 1 := le_antisymm hUle (not_lt.mp fun h => hu ((hA u).mp h))
  set s : Ω := τ'⁻¹ t with hsdef
  have hs : τ' s = t := by
    show τ' (τ'⁻¹ t) = t
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hsn : s ^ (normV v - 1) = U := by
    show (τ'⁻¹ t) ^ (normV v - 1) = U
    rw [← map_pow, ht, hUdef, AlgEquiv.commutes]
  have hvs : A.valuation s = 1 := by
    have h : A.valuation s ^ (normV v - 1) = 1 := by rw [← map_pow, hsn, hU1]
    exact (pow_eq_one_iff.mp h).resolve_right (by omega)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hF : A.valuation (t - s ^ normV v) < 1 := by
    have := hτ'.2 s hvs.le
    rwa [hs] at this
  have hinv : τ'⁻¹ π * s = π * t := by
    rw [hsdef, ← map_mul]
    calc τ'⁻¹ (π * t) = τ'⁻¹ (τ' (π * t)) := by rw [h2]
      _ = π * t := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hrat : (τ'⁻¹ * τ) π = τ'⁻¹ π := by rw [AlgEquiv.mul_apply, h1]
  have hqs : s ^ normV v = U * s := by
    rw [← hsn, ← pow_succ]; congr 1; omega
  have key : (τ'⁻¹ * τ) π / π - U = (t - s ^ normV v) / s := by
    rw [hrat, hqs]
    have e : τ'⁻¹ π = π * t / s := by rw [eq_div_iff hs0, hinv]
    rw [e]
    field_simp
  rw [key, map_div₀, hvs, div_one]
  exact hF

end GlobalTheory.TameRatio

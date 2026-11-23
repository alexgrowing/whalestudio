import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ConjCount
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Residue

open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

theorem exists_unit_div_conj (v : HeightOneSpectrum (𝓞 K)) {A b : IdealGroup K}
    (hA : A ∈ primeTo v) (hb : b ∈ fromBase K) {α : Kˣ}
    (h : A = toPrincipalIdeal (𝓞 K) K α * b) :
    ∃ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (α : K) / complexConj K (α : K) := by
  have hc : complexConj K (α : K) ≠ 0 := by
    simp
  have key := (exists_unit_locAt_iff v (α / Units.mk0 _ hc)).mpr ?_
  · simpa using key
  obtain ⟨h1, h2⟩ := hA
  subst h
  have hb' := count_fromBase v hb
  have hα := count_spanSingleton_conj v (α : K)
  rw [Units.val_mul, FractionalIdeal.count_mul K _ (Units.ne_zero _) (Units.ne_zero _),
    coe_toPrincipalIdeal] at h1 h2
  rw [div_eq_mul_inv, map_mul, map_inv, Units.val_mul,
    FractionalIdeal.count_mul K _ (Units.ne_zero _) (Units.ne_zero _), Units.val_inv_eq_inv_val,
    FractionalIdeal.count_inv, coe_toPrincipalIdeal, coe_toPrincipalIdeal, Units.val_mk0, hα]
  omega

end KStar.IdealValuations

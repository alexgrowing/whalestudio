import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem normV_zpow_deg_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (σ' : Weil h') (σ : Weil h) (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v' : ℕ) : ℝ) ^ deg σ' = ((normV v : ℕ) : ℝ) ^ deg σ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, ha⟩ := σ'.2
  obtain ⟨c, d, hc⟩ := σ.2
  rw [deg_eq ha, deg_eq hc]
  set q' := normV v' with hq'
  set q := normV v with hq
  have hq'0 : 0 < q' := (zero_lt_one.trans (one_lt_normV v'))
  have hq0 : 0 < q := (zero_lt_one.trans (one_lt_normV v))
  have key : ∀ x : Ω, A.valuation x ≤ 1 →
      A.valuation (x ^ (q' ^ a * q ^ d) - x ^ (q ^ c * q' ^ b)) < 1 := by
    intro x hx
    have hy : A.valuation ((σ' : G L Ω) x) ≤ 1 := val_apply_le_one ha.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (ha.2 x hx) (q ^ d)
    have h2' := hc.2 x hx
    rw [hσ] at h2'
    have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2' (q' ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h2
    rw [mul_comm (q ^ d) (q' ^ b)] at h2
    exact cong_trans (cong_symm h1) h2
  have hN : q' ^ a * q ^ d = q ^ c * q' ^ b := by
    rcases lt_trichotomy (q' ^ a * q ^ d) (q ^ c * q' ^ b) with hlt | heq | hgt
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq'0 a) (pow_pos hq0 d)) hlt
      exact absurd (cong_symm (key x hx)) hx'
    · exact heq
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq0 c) (pow_pos hq'0 b)) hgt
      exact absurd (key x hx) hx'
  have hR : ((q' : ℕ) : ℝ) ^ a * ((q : ℕ) : ℝ) ^ d = ((q : ℕ) : ℝ) ^ c * ((q' : ℕ) : ℝ) ^ b := by
    exact_mod_cast hN
  have h1 : ((q' : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  rw [zpow_sub₀ h1, zpow_sub₀ h2, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h2)]
  linarith

end GlobalTheory.LocLanglands

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

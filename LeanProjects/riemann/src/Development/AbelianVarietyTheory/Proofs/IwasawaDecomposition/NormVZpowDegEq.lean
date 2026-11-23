import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EpsInduction

section Norm

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω}

theorem pow_mul_pow_eq [IsAlgClosed Ω] {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {σ : G K Ω} {σ' : G L Ω}
    (hσ : ∀ z, σ z = σ' z) {a b c e : ℕ} (H : ActsAs A q σ a b) (H' : ActsAs A q' σ' c e) :
    q ^ a * q' ^ e = q' ^ c * q ^ b := by
  have key : ∀ x, A.valuation x ≤ 1 → A.valuation (x ^ (q ^ a * q' ^ e) - x ^ (q' ^ c * q ^ b)) < 1 := by
    intro x hx
    have hy := val_apply_le_one H.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (H.2 x hx) (q' ^ e)
    have h2 := H'.2 x hx
    rw [← hσ] at h2
    have h3 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2 (q ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h3
    rw [mul_comm (q' ^ e)] at h3
    exact cong_trans (cong_symm h1) h3
  rcases lt_trichotomy (q ^ a * q' ^ e) (q' ^ c * q ^ b) with hlt | heq | hlt
  · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (by positivity) hlt
    exact absurd (cong_symm (key x hx)) hx'
  · exact heq
  · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (by positivity) hlt
    exact absurd (key x hx) hx'

end Norm

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L]
  [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}

theorem normV_zpow_deg_eq {σ : Weil h} {σ' : Weil h'} (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v : ℕ) : ℝ) ^ deg σ = ((normV v' : ℕ) : ℝ) ^ deg σ' := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, H⟩ := σ.2
  obtain ⟨c, e, H'⟩ := σ'.2
  have hq : 0 < normV v := zero_lt_one.trans (one_lt_normV v)
  have hq' : 0 < normV v' := zero_lt_one.trans (one_lt_normV v')
  have key := pow_mul_pow_eq hq hq' hσ H H'
  have hr : (0 : ℝ) < (normV v : ℕ) := by exact_mod_cast hq
  have hr' : (0 : ℝ) < (normV v' : ℕ) := by exact_mod_cast hq'
  rw [deg_eq H, deg_eq H', zpow_sub₀ hr.ne', zpow_sub₀ hr'.ne', div_eq_div_iff (by positivity) (by positivity),
    zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
  exact_mod_cast key

theorem normV_cpow_deg_eq (s : ℝ) {σ : Weil h} {σ' : Weil h'} (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    (((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ = (((normV v' : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ' := by
  have key : ∀ (q : ℕ) (k : ℤ), ((q : ℂ) ^ (s : ℂ)) ^ k = ((((q : ℝ) ^ k) ^ s : ℝ) : ℂ) := fun q k => by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    rw [← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow,
      Complex.ofReal_cpow hq, Complex.ofReal_natCast]
  rw [key, key, normV_zpow_deg_eq hσ]

def forgetN {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h V where
  ρ := a.ρ
  N := 0
  smooth := a.smooth
  semisimple := a.semisimple
  nilpotent := IsNilpotent.zero
  comm σ := by simp

end GlobalTheory.EpsInduction

end

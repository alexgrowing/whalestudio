import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.GalUnitCompat
import Development.DiscreteGroups.GlobalIrreducibility.DzGalEig
import Development.DiscreteGroups.GlobalIrreducibility.DzGalInd
import Development.DiscreteGroups.GlobalIrreducibility.LpTwistLpTwist
import Development.DiscreteGroups.GlobalIrreducibility.DzGalChi
import Development.DiscreteGroups.GlobalIrreducibility.DzGalUnr
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ResIso : Prop :=
  ∀ (L E' Ω : Type) [Field L] [NumberField L] [Field E'] [NumberField E'] [Field Ω] [Algebra L Ω] [Algebra E' Ω]
    [IsAlgClosure L Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime] (n : ℕ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    normV v = g ^ n → normV w' = g ^ n →
    ∀ (K : Type) [Field K] (red : 𝓞 E' →+* K), Function.Surjective red → RingHom.ker red = w'.asIdeal →
    ∃ κ : 𝓀[v.adicCompletion L] ≃+* K, ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x

theorem lpOfChar_congr {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {χ χ' : Weil h →* ℂˣ} (e : χ = χ')
    (hχ : IsSmooth χ) (hχ' : IsSmooth χ') : WD.lpOfChar h χ hχ = WD.lpOfChar h χ' hχ' := by
  subst e; rfl

theorem regular_ne_one {g n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] {ξ : Kˣ →* ℂˣ}
    (hξ : GlobalTheory.Published.IsRegularChar g n ξ) : ξ ≠ 1 := by
  intro h1
  have := hξ 0 1 (by omega) (by omega) (by rw [h1, one_pow, one_pow])
  omega

theorem nmChar_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) :
    nmChar K χ₀ ^ g = nmChar K χ₀ := by
  ext z
  simp only [MonoidHom.pow_apply, nmChar, MonoidHom.comp_apply, ← map_pow]
  congr 2
  ext
  simp [ZMod.pow_card]

theorem regular_mul_nm_ne_one {g n : ℕ} [Fact g.Prime] (hn : 2 ≤ n) {K : Type} [Field K] [Algebra (ZMod g) K]
    {ξ : Kˣ →* ℂˣ} (hξ : GlobalTheory.Published.IsRegularChar g n ξ) (χ₀ : (ZMod g)ˣ →* ℂˣ) : ξ * nmChar K χ₀ ≠ 1 := by
  intro h1
  have hξe : ξ = (nmChar K χ₀)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have := hξ 0 1 (by omega) (by omega) (by rw [hξe, pow_zero, pow_one, pow_one, inv_pow, nmChar_pow])
  omega

end DiscreteGroups.sglob.DzType

end

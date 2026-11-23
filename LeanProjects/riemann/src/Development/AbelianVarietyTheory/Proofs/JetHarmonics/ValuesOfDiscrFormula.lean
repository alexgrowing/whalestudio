import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.DiffAtOddSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.RelativeDifferentValues
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuadraticFieldDiscPrimeThreeModFour

open NumberField IsDedekindDomain UniqueFactorizationMonoid IntermediateField
open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.IndefiniteRowSideFullHecke.RelativeDifferentValues

namespace GlobalTheory.DifferentExponentCompare

section Dictionary

variable {E : Type} [Field E] [NumberField E]

theorem exists_cofactor_iff {ℓ : ℕ} (hℓ : ℓ.Prime) (a : ℕ) :
    (∃ m : ℕ, ¬ ℓ ∣ m ∧ (discr E).natAbs = ℓ ^ a * m) ↔ padicValInt ℓ (discr E) = a := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  unfold padicValInt
  constructor
  · rintro ⟨m, hm, h⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    rw [h, padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  · rintro rfl
    obtain ⟨m, hm⟩ : ℓ ^ padicValNat ℓ (discr E).natAbs ∣ (discr E).natAbs := pow_padicValNat_dvd
    refine ⟨m, fun ⟨k, hk⟩ => ?_, hm⟩
    refine pow_succ_padicValNat_not_dvd (p := ℓ) h0 ⟨k, ?_⟩
    rw [pow_succ, mul_assoc, ← hk, ← hm]

end Dictionary

def ValueAtTwo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e : ℕ),
    Module.finrank ℚ E = 2 ^ (e + 2) → rootDiscrVal_vp E 2 = (e : ℚ) + 1 - 1 / (2 : ℚ) ^ e →
    ∀ P : HeightOneSpectrum (𝓞 E), ((2 : ℕ) : 𝓞 E) ∈ P.asIdeal →
      vd_vp 2 P = (e : ℚ) + 1 - 1 / (2 : ℚ) ^ e

def ValueHalf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e ℓ : ℕ), ℓ.Prime →
    Module.finrank ℚ E = 2 ^ (e + 2) → rootDiscrVal_vp E ℓ = 1 / 2 →
    ∀ P : HeightOneSpectrum (𝓞 E), (ℓ : 𝓞 E) ∈ P.asIdeal → vd_vp ℓ P = 1 / 2

end GlobalTheory.DifferentExponentCompare

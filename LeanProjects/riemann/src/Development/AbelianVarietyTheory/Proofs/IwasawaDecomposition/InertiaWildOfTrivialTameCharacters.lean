import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

namespace GlobalTheory.TameWild

theorem sub_one_lt_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [hg : Fact g.Prime]
    (hvg : A.valuation (g : Ω) < 1) {z : Ω} (a : ℕ) (hz : A.valuation (z ^ (g ^ a) - 1) < 1) :
    A.valuation (z - 1) < 1 := by
  have hz1 : A.valuation z ≤ 1 := by
    have h : A.valuation (z ^ g ^ a) ≤ 1 := by
      have e : z ^ g ^ a = (z ^ g ^ a - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hz.le (by simp))
    rw [map_pow] at h
    by_contra hc
    push Not at hc
    exact absurd h (not_le.2 (one_lt_pow' hc (pow_ne_zero _ hg.out.ne_zero)))
  have hzA : z ∈ A := (A.valuation_le_one_iff z).1 hz1
  let zA : A := ⟨z, hzA⟩
  haveI : CharP (IsLocalRing.ResidueField A) g := by
    rw [CharP.charP_iff_prime_eq_zero hg.out, ← map_natCast (IsLocalRing.residue A),
      IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hvg
  have h1 : IsLocalRing.residue A (zA ^ g ^ a - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa [zA] using hz
  have h2 : IsLocalRing.residue A (zA - 1) = 0 := by
    apply pow_eq_zero_iff (n := g ^ a) (pow_ne_zero _ hg.out.ne_zero) |>.1
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, ← map_one (IsLocalRing.residue A), ← map_sub, h1]
  rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h2
  simpa [zA] using h2

open GlobalTheory.TameInertiaGen in

theorem cob_lt_one_of_tame : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv τ hτ hroot y hy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this
  obtain ⟨p, hp0, hp⟩ := exists_nat_gen A
  have halg : IsAlgebraic ℤ y := by
    have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, k, hm, hk⟩ := exists_pow_eq A hp0 hp hy halg
  obtain ⟨e, he⟩ := hp g hg.out.ne_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [he, pow_zero] at hvg
    exact lt_irrefl _ hvg
  have hM0 : m * e ≠ 0 := mul_ne_zero hm he0
  have hM : A.valuation y ^ (m * e) = A.valuation (g : Ω) ^ k := by
    rw [pow_mul, hk, he, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  obtain ⟨a, m', hm', hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 g hg.out.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hm' (dvd_zero _)
  set d := m'.totient with hd
  have hdpos : 0 < d := Nat.totient_pos.2 (Nat.pos_of_ne_zero hm'0)
  have hcop : g.Coprime m' := (Nat.Prime.coprime_iff_not_dvd hg.out).2 hm'
  have hdvd : m' ∣ g ^ d - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hg.out.pos)).1 (Nat.ModEq.pow_totient hcop).symm
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨r, hr, hrτ⟩ := hroot d hdpos
  have hN : g ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hdpos.ne' hg.out.one_lt
    omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hr
    exact hg.out.ne_zero (by exact_mod_cast hr.symm)
  have hR : cob τ (Units.mk0 r hr0) ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0]
    exact hrτ
  have hval : A.valuation ((Units.mk0 (y ^ g ^ a) (pow_ne_zero _ hy) : Ωˣ) : Ω) =
      A.valuation ((Units.mk0 r hr0 : Ωˣ) : Ω) ^ ((c : ℤ) * k) := by
    rw [Units.val_mk0, Units.val_mk0, ← pow_left_inj₀ zero_le zero_le hm'0, map_pow, ← pow_mul, ← hM', hM, ← hr,
      map_pow, hc, ← zpow_natCast (A.valuation r) (m' * c),
      ← zpow_natCast (A.valuation r ^ ((c : ℤ) * k)) m', ← zpow_mul, ← zpow_mul]
    congr 1
    push_cast
    ring
  have h1 := cob_mem_of_zpow hτ hR hval
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0, map_pow, ← div_pow] at h1
  exact sub_one_lt_one_of_pow A hvg a h1

end GlobalTheory.TameWild

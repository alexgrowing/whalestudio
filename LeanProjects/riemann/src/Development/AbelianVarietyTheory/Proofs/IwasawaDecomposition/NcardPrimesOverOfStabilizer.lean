import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.FrobeniusOrbits.HostCorollaries

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise

namespace GlobalTheory.HostSplit

theorem jacobiSym_neg_eq_one {r p : ℕ} (hr : r % 2 = 1) (h4 : p % 4 = 1) (h1 : p % r = 1) :
    jacobiSym (-(r : ℤ)) p = 1 := by
  have hgo : Odd p := Nat.odd_iff.mpr (by omega)
  have hdo : Odd r := Nat.odd_iff.mpr hr
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h2 : ((p : ℤ) % (r : ℤ)) = 1 := by
    rw [← Int.natCast_mod, h1]
    rfl
  rw [h2, jacobiSym.one_left]

theorem ncard_placesOver (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).ncard = (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have himg : HeightOneSpectrum.asIdeal '' placesOver E p =
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hPp := v.isPrime
      refine ⟨hPp, ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · rintro ⟨h1, h2⟩
      refine ⟨⟨P, h1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
      have h3 : (p : ℤ) ∈ P.under ℤ := by
        rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 : algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P := h3
      rw [map_natCast] at h4
      exact h4
  rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]

theorem ncard_primesOver_of_stabilizer (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ σ : E ≃ₐ[ℚ] E, σ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E) P → σ = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hr : Set.range (fun σ : E ≃ₐ[ℚ] E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have hinj : Function.Injective (fun σ : E ≃ₐ[ℚ] E => σ • P) := by
    intro σ τ hστ
    have h1 : τ⁻¹ * σ = 1 := by
      apply h
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      have h2 : σ • P = τ • P := hστ
      rw [h2, inv_smul_smul]
    exact (inv_mul_eq_one.mp h1).symm
  rw [← hr, Set.ncard_range_of_injective hinj, IsGalois.card_aut_eq_finrank]

theorem split_of_one_mod : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → p % (H.QS * H.q * H.d) = 1 →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK := by
  intro R H p hp hc
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hmod : ∀ m : ℕ, 1 < m → m ∣ H.QS * H.q * H.d → p % m = 1 := by
    intro m hm hdv
    rw [← Nat.mod_mod_of_dvd p hdv, hc]
    exact Nat.mod_eq_of_lt hm
  have h4Q : 4 ∣ H.QS := (show (2 : ℕ) ^ 2 ∣ 2 ^ (R.e + 2) from pow_dvd_pow 2 (by omega)).trans H.tower_dvd
  have h4 : p % 4 = 1 := hmod 4 (by norm_num) ((h4Q.mul_right _).mul_right _)
  have hd : p % H.d = 1 := hmod _ (by omega) (dvd_mul_left _ _)
  have hnd : ∀ m : ℕ, m ∣ H.QS * H.q * H.d → ¬ p ∣ m := by
    intro m hm hpm
    have h := hmod p hp.one_lt (hpm.trans hm)
    rw [Nat.mod_self] at h
    omega
  have hN : ¬ p ∣ H.condN := hnd _ dvd_rfl
  have hp2 : p ∉ H.small := fun h =>
    hnd H.QS (((dvd_refl _).mul_right _).mul_right _) (Nat.dvd_of_mem_primeFactors h)
  have hpq : p ≠ H.q := fun h => hnd H.q ((dvd_mul_left _ _).mul_right _) (h ▸ dvd_rfl)
  have hpd : p ≠ H.d := fun h => hnd H.d (dvd_mul_left _ _) (h ▸ dvd_rfl)
  have jd := jacobiSym_neg_eq_one (r := H.d) (by omega) h4 hd
  refine ⟨?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hG : IsGalois ℚ H.E := H.galois
    have := Formalism.FrobeniusOrbits.SplitK.span_prime p
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
    obtain ⟨-, hF, -, hI⟩ := H.der.frob p hN P
    have h1 : IsArithFrobAt ℤ (1 : H.E ≃ₐ[ℚ] H.E) P := by
      refine (hF 1 1 ?_).2 (by rw [map_one, map_one])
      rw [← ZMod.natCast_mod p, show p % H.condN = 1 from hc]
      simp
    rw [ncard_placesOver H.E hp]
    refine ncard_primesOver_of_stabilizer H.E p P fun σ hσ => ?_
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p P 1 σ h1 hσ
    rw [(hI ρ).1 hρ, one_pow, mul_one]
  · unfold Host.cls primeClass
    rw [if_neg hp2, if_neg hpq, if_neg hpd, if_pos jd]

end GlobalTheory.HostSplit

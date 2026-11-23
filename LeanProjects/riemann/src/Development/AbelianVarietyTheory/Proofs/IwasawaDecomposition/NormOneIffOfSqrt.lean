import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRatAddMulOfMemAdjoin
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem half_int_coords {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (a b : ℚ)
    (hy : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    ∃ t u : ℤ, (2 : ℤ) ∣ t - u ∧ 2 * a = t ∧ 2 * b = u := by
  have hcy : IsIntegral ℤ ((a : E) - (b : E) * s) := by
    have := hy.map (c.toRingEquiv.toRingHom.toIntAlgHom)
    simpa [hc, sub_eq_add_neg] using this
  have key : ∀ q : ℚ, IsIntegral ℤ (q : E) → ∃ n : ℤ, q = n := by
    intro q hq
    have h1 : IsIntegral ℤ q := by
      have : (q : E) = algebraMap ℚ E q := by simp
      rw [this] at hq
      exact (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hq
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    exact ⟨n, by simpa using hn.symm⟩
  obtain ⟨t, ht⟩ := key (2 * a) (by
    have e : ((2 * a : ℚ) : E) = ((a : E) + (b : E) * s) + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]; exact hy.add hcy)
  obtain ⟨n, hn⟩ := key (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E) = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast; linear_combination (b : E) ^ 2 * hs
    rw [e]; exact hy.mul hcy)
  have hm : (d : ℚ) * (2 * b) ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [← ht, ← hn]; ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * b) = k := by
    have h1 : IsIntegral ℤ (((d : ℚ) * (2 * b)) ^ 2) := by
      have : ((d : ℚ) * (2 * b)) ^ 2 = algebraMap ℤ ℚ (d * (4 * n - t ^ 2)) := by
        rw [eq_intCast, Int.cast_mul, ← hm]; push_cast; ring
      rw [this]; exact isIntegral_algebraMap
    have h2 := IsIntegral.of_pow (by norm_num : 0 < 2) h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨n, by simpa using hn.symm⟩
  have hk2 : k ^ 2 = (d : ℤ) * (4 * n - t ^ 2) := by
    have : (k : ℚ) ^ 2 = (d : ℚ) * ((4 * n - t ^ 2 : ℤ) : ℚ) := by
      rw [← hm, ← hk]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (hk2 ▸ dvd_mul_right _ _)
  obtain ⟨u, rfl⟩ := hdk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hu : 2 * b = u := by
    apply mul_left_cancel₀ hd0
    rw [hk]; push_cast; ring
  refine ⟨t, u, ?_, ht, hu⟩
  have h5 : (d : ℤ) * u ^ 2 = 4 * n - t ^ 2 := by
    rw [hu] at hm; exact_mod_cast hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e + 3 := ⟨(d : ℤ) / 4, by omega⟩
  have h6 : (2 : ℤ) ∣ (t - u) ^ 2 := ⟨2 * n - (2 * e + 1) * u ^ 2 - t * u, by
    rw [he] at h5; linear_combination h5⟩
  exact Int.prime_two.dvd_of_dvd_pow h6

theorem exists_rat_coords {E : Type} [Field E] [NumberField E] (d : ℕ)
    (s : E) (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ {s}) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s :=
  _root_.GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin d s hs hx

theorem normOne_iff_of_sqrt {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (M p : ℕ) :
    NormOne d M p ↔ ∃ π : 𝓞 E, (π : E) ∈ IntermediateField.adjoin ℚ {s} ∧ (π : E) * c (π : E) = (p : E) ∧
      (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)} := by
  have hsK : s ∈ IntermediateField.adjoin ℚ {s} := IntermediateField.mem_adjoin_simple_self ℚ _
  constructor
  · rintro ⟨A, B, hN, ⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) + 1 = 4 * e := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have heE : (d : E) + 1 = 4 * e := by exact_mod_cast congrArg (Int.cast : ℤ → E) he
    have hω : IsIntegral ℤ ((1 + s) / 2) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e, by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, eq_intCast]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * heE
    let ω : 𝓞 E := ⟨(1 + s) / 2, hω⟩
    have hA : (A : E) = 2 + M * u + 2 * M * v := by
      have : A = 2 + M * u + 2 * M * v := by linear_combination hv + hu
      rw [this]; push_cast; ring
    have hB : (B : E) = M * u := by rw [hu]; push_cast; ring
    have hπ : ((1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω) : 𝓞 E) : E) = ((A : E) + B * s) / 2 := by
      have h0 : algebraMap (𝓞 E) E ω = (1 + s) / 2 := rfl
      change algebraMap (𝓞 E) E _ = _
      simp only [map_add, map_mul, map_one, map_natCast, map_intCast]
      rw [h0, hA, hB]; ring
    refine ⟨1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω), ?_, ?_, ?_⟩
    · rw [hπ]
      exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hsK)) (ofNat_mem _ 2)
    · rw [hπ]
      have hNE : (A : E) ^ 2 + d * B ^ 2 = 4 * p := by exact_mod_cast congrArg (Int.cast : ℤ → E) hN
      rw [map_div₀, map_add, map_mul, map_intCast, map_intCast, hc, map_ofNat]
      linear_combination (1 / 4 : E) * hNE - (B : E) ^ 2 / 4 * hs
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨π, hK, hN, hM⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hM
    have hyE : (π : E) = 1 + M * (y : E) := by
      have : π = 1 + M * y := by linear_combination hy
      rw [this]; push_cast; rfl
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · rw [hyE] at hN
      simp only [Nat.cast_zero, zero_mul, add_zero, map_one, mul_one] at hN
      have : p = 1 := by exact_mod_cast hN.symm
      exact ⟨2, 0, by simp [this], by simp, by simp⟩
    · have hME : (M : E) ≠ 0 := by exact_mod_cast hM0.ne'
      have hyK : (y : E) ∈ IntermediateField.adjoin ℚ {s} := by
        have : (y : E) = ((π : E) - 1) / M := by rw [hyE]; field_simp; ring
        rw [this]
        exact div_mem (sub_mem hK (one_mem _)) (natCast_mem _ _)
      obtain ⟨a, b, hab⟩ := exists_rat_coords d s hs hyK
      obtain ⟨t, u, ⟨w, hw⟩, ht, hu⟩ := half_int_coords d hd h4 s hs c hc a b (hab ▸ y.isIntegral_coe)
      have htE : 2 * (a : E) = t := by exact_mod_cast congrArg (Rat.cast : ℚ → E) ht
      have huE : 2 * (b : E) = u := by exact_mod_cast congrArg (Rat.cast : ℚ → E) hu
      refine ⟨2 + M * t, M * u, ?_, dvd_mul_right _ _, ⟨w, by linear_combination (M : ℤ) * hw⟩⟩
      rw [hyE, hab] at hN
      simp only [map_add, map_mul, map_one, map_natCast, map_ratCast, hc] at hN
      have : (2 + M * t : E) ^ 2 + d * (M * u) ^ 2 = 4 * p := by
        rw [← htE, ← huE]
        linear_combination 4 * hN + 4 * (M : E) ^ 2 * (b : E) ^ 2 * hs
      exact_mod_cast this

theorem normOne_iff_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), NormOne H.d M p ↔ ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)} := by
  intro R H M p
  have hs : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hc : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
    apply H.φ₀.injective
    have h1 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h2 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) :=
      H.conjE_apply _ _
    rw [h2, map_neg, h1]
    simp
  exact normOne_iff_of_sqrt H.d H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqrtMinusD hs H.conj hc M p

end GlobalTheory.Mem.An

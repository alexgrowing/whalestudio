import Formalism.LocalToGlobal.Divisibility.JetBounds.EmbExists
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormInvNatCastLeOfDvd
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.DworkPowerSeriesWeights

namespace EmbeddingLemmas

theorem norm_le_one_of_isIntegral {k : Type} [NormedField k] [IsUltrametricDist k] {y : k}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hev⟩ := hy
  have hsumle : ∀ (s : Finset ℕ) (f : ℕ → k) (C : ℝ), 0 ≤ C → (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C := by
    intro s f C hC
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hC
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hev
  have hyn := eq_neg_of_add_eq_zero_left hev
  have hy1 : (1 : ℝ) ≤ ‖y‖ := hlt.le
  by_cases hn : p.natDegree = 0
  · rw [hn, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at hyn
    exact one_ne_zero hyn
  have hb : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ k) y (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖y‖ ^ (p.natDegree - 1) := by
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ k) (p.coeff i)‖ ≤ 1 := by
      rw [algebraMap_int_eq, eq_intCast]
      exact IsUltrametricDist.norm_intCast_le_one k _
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.1 hi
      omega
    calc ‖(algebraMap ℤ k) (p.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (p.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hy1 hi') (by positivity) zero_le_one
      _ = ‖y‖ ^ (p.natDegree - 1) := one_mul _
  have hle := hsumle _ _ _ (by positivity) hb
  have hle' : ‖y‖ ^ p.natDegree ≤ ‖y‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, hyn, norm_neg]
    exact hle
  have hlt' : ‖y‖ ^ (p.natDegree - 1) < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith [hle']

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cAdd (x y : 𝓞 K) : ((x + y : 𝓞 K) : K) = (x : K) + (y : K) := map_add (algebraMap (𝓞 K) K) x y

theorem cMul (x y : 𝓞 K) : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := map_mul (algebraMap (𝓞 K) K) x y

theorem cZero : ((0 : 𝓞 K) : K) = 0 := map_zero (algebraMap (𝓞 K) K)

theorem cNat (n : ℕ) : ((n : 𝓞 K) : K) = (n : K) := by simp

theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) (m : ℕ) :
    x ∈ w.asIdeal ^ m ↔ (m : ℤ) ≤ vw w (x : K) := by
  classical
  have hspan : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_int, FractionalIdeal.count_coe K w hspan, Nat.cast_le,
    ← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hspan) w.associates_irreducible

theorem exists_clear (w : HeightOneSpectrum (𝓞 K)) (b : K) (hb : 0 ≤ vw w b) :
    ∃ c z : 𝓞 K, c ∉ w.asIdeal ∧ (c : K) * b = (z : K) := by
  by_cases hb0 : b = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · rw [hb0, mul_zero, cZero]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : (algebraMap (𝓞 K) K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxK : (algebraMap (𝓞 K) K x) ≠ 0 := fun h => hb0 (by rw [h, zero_div])
  have hx0 : x ≠ 0 := fun h => hxK (by rw [h, map_zero])
  have hvy : 0 ≤ vw w (algebraMap (𝓞 K) K y) := ValuationRepresentative.vw_int_nonneg w y
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hvy
  rw [div_eq_mul_inv, ValuationRepresentative.vw_mul w _ _ hxK (inv_ne_zero hyK), ValuationRepresentative.vw_inv] at hb
  have hxm : x ∈ w.asIdeal ^ m := (mem_pow_iff w x hx0 m).2 (by
    change (m : ℤ) ≤ vw w (algebraMap (𝓞 K) K x)
    omega)
  have hym : y ∈ w.asIdeal ^ m := (mem_pow_iff w y hy0 m).2 (by
    change (m : ℤ) ≤ vw w (algebraMap (𝓞 K) K y)
    omega)
  have hym1 : y ∉ w.asIdeal ^ (m + 1) := fun h => by
    have h2 := (mem_pow_iff w y hy0 (m + 1)).1 h
    change ((m + 1 : ℕ) : ℤ) ≤ vw w (algebraMap (𝓞 K) K y) at h2
    push_cast at h2
    omega
  have hdvd : w.asIdeal ^ m ∣ Ideal.span {y} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hym
  obtain ⟨J, hJ⟩ := hdvd
  have hJw : ¬ J ≤ w.asIdeal := fun h => by
    apply hym1
    have h1 : y ∈ w.asIdeal ^ m * J := by
      rw [← hJ]
      exact Ideal.mem_span_singleton_self y
    rw [pow_succ]
    exact Ideal.mul_mono_right h h1
  obtain ⟨c, hcJ, hcw⟩ := SetLike.not_le_iff_exists.1 hJw
  have hxc : x * c ∈ Ideal.span {y} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hxm hcJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hxc
  refine ⟨c, z, hcw, ?_⟩
  have hz' : (algebraMap (𝓞 K) K z) * (algebraMap (𝓞 K) K y) =
      (algebraMap (𝓞 K) K x) * (algebraMap (𝓞 K) K c) := by
    rw [← map_mul, ← map_mul, hz]
  change (algebraMap (𝓞 K) K c) * _ = algebraMap (𝓞 K) K z
  field_simp
  linear_combination -hz'

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le (σ : K →+* ℂ_[l]) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  obtain ⟨p, hp, hpx⟩ := NumberField.RingOfIntegers.isIntegral_coe x
  refine norm_le_one_of_isIntegral ⟨p, hp, ?_⟩
  have h := congrArg σ hpx
  rw [map_zero, Polynomial.hom_eval₂] at h
  have h2 : Polynomial.eval₂ (Int.castRingHom ℂ_[l]) (σ x) p = 0 := by
    rw [← RingHom.ext_int (σ.comp (algebraMap ℤ K)) (Int.castRingHom ℂ_[l])]
    exact h
  exact h2

def normIdeal (σ : K →+* ℂ_[l]) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [cAdd, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [cZero, map_zero, norm_zero]
    exact one_pos
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul, cMul, map_mul, norm_mul]
    calc ‖σ (c : K)‖ * ‖σ (x : K)‖ ≤ 1 * ‖σ (x : K)‖ :=
          mul_le_mul_of_nonneg_right (norm_int_le σ c) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

end EmbeddingLemmas

theorem embeddingForces_holds : EmbForces := by
  intro K _ _ _ w l hlp ι h
  by_contra hne
  have hnot : (l : 𝓞 K) ∉ w.asIdeal := by
    intro hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
    have hdvd : plc w ∣ l := (ringChar.spec (𝓞 K ⧸ w.asIdeal) l).1 hmem
    exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.ramBasic K w).1 hlp.out).1 hdvd)
  have hv : vw w (l : K) = 0 := by
    have h2 := ValuationZeroReduction.vw_eq_zero_of_not_mem w (l : 𝓞 K) hnot
    rwa [EmbeddingLemmas.cNat] at h2
  have h3 := h (l : K) (Nat.cast_ne_zero.2 hlp.out.ne_zero)
  rw [map_natCast, hv, Int.cast_zero, zero_div, Real.rpow_zero] at h3
  exact absurd h3 (norm_l_lt_one l).ne

end Formalism.L2.DIV

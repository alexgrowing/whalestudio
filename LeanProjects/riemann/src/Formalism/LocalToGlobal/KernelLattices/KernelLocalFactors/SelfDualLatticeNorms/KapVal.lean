import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime

noncomputable section
open NumberField IsDedekindDomain

namespace Formalism.L2.Ker.KS

section Val

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p])

theorem normO_le (a : 𝓞 K) : ‖f (a : K)‖ ≤ 1 := by
  obtain ⟨P, hm, hP⟩ := RingOfIntegers.isIntegral_coe a
  let v : Valuation ℂ_[p] NNReal := NormedField.valuation
  have hv := Valuation.integer.integers v
  have h2 : IsIntegral v.integer (f (a : K)) := by
    refine ⟨P.map (Int.castRingHom v.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e1 : (algebraMap v.integer ℂ_[p]).comp (Int.castRingHom v.integer) = f.comp (algebraMap ℤ K) :=
      RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (algebraMap ℤ K) (a : K) P = 0 := hP
    rw [this, map_zero]
  have := (hv.isIntegral_iff_v_le_one).mp h2
  exact_mod_cast this

variable (𝔭 : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (h : ℕ) (hgen : 𝔭.asIdeal ^ h = Ideal.span {ϖ}) (hlt : ‖f (ϖ : K)‖ < 1)

include hgen hlt in

theorem norm_lt_of_mem {t : 𝓞 K} (ht : t ∈ 𝔭.asIdeal) : ‖f (t : K)‖ < 1 := by
  have hmem : t ^ h ∈ Ideal.span {ϖ} := hgen ▸ Ideal.pow_mem_pow ht h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have key : ‖f (t : K)‖ ^ h < 1 := by
    have e : ‖f (t : K)‖ ^ h = ‖f (c : K)‖ * ‖f (ϖ : K)‖ := by
      rw [← norm_pow, ← map_pow, ← norm_mul, ← map_mul]
      congr 2
      exact_mod_cast hc.symm
    rw [e]
    calc ‖f (c : K)‖ * ‖f (ϖ : K)‖ ≤ 1 * ‖f (ϖ : K)‖ :=
          mul_le_mul_of_nonneg_right (normO_le f c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hlt
  have hh : h ≠ 0 := by
    rintro rfl
    simp at key
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hh).mp key

include hgen hlt in

theorem norm_eq_one_of_not_mem {a : 𝓞 K} (ha : a ∉ 𝔭.asIdeal) : ‖f (a : K)‖ = 1 := by
  obtain ⟨b, i, hi, hbi⟩ := 𝔭.isMaximal.exists_inv ha
  have hsmall : ‖f (i : K)‖ < 1 := norm_lt_of_mem f 𝔭 ϖ h hgen hlt hi
  have hba : ‖f (b : K)‖ * ‖f (a : K)‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    have e : ((b : K) * (a : K)) = 1 + -(i : K) := by
      have : ((b * a + i : 𝓞 K) : K) = 1 := by rw [hbi]; rfl
      push_cast at this
      linear_combination this
    rw [e, map_add, map_neg, map_one]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_neg] <;> linarith [hsmall]
  refine le_antisymm (normO_le f a) ?_
  calc (1 : ℝ) = ‖f (b : K)‖ * ‖f (a : K)‖ := hba.symm
    _ ≤ 1 * ‖f (a : K)‖ := mul_le_mul_of_nonneg_right (normO_le f b) (norm_nonneg _)
    _ = ‖f (a : K)‖ := one_mul _

include hgen hlt in

theorem norm_pow_int {a : 𝓞 K} (ha : a ≠ 0) :
    ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) ∧ ‖f (a : K)‖ ^ h = ‖f (ϖ : K)‖ ^ n := by
  classical
  obtain ⟨n, hva⟩ : ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) := ⟨_, 𝔭.intValuation_if_neg ha⟩
  refine ⟨n, hva, ?_⟩
  have hvah : 𝔭.intValuation (a ^ h) = WithZero.exp (-((n * h : ℕ) : ℤ)) := by
    rw [map_pow, hva, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have hmem : a ^ h ∈ Ideal.span {ϖ ^ n} := by
    have := (𝔭.intValuation_le_pow_iff_mem (a ^ h) (n * h)).mp hvah.le
    rwa [mul_comm, pow_mul, hgen, Ideal.span_singleton_pow] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcn : c ∉ 𝔭.asIdeal := by
    intro hcm
    have h1 : a ^ h ∈ 𝔭.asIdeal ^ (n * h + 1) := by
      rw [← hc, pow_succ', mul_comm n h, pow_mul, hgen, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_mul hcm (Ideal.mem_span_singleton_self _)
    have h2 := (𝔭.intValuation_le_pow_iff_mem _ _).mpr h1
    rw [hvah, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hc1 := norm_eq_one_of_not_mem f 𝔭 ϖ h hgen hlt hcn
  have e : (a : K) ^ h = (c : K) * (ϖ : K) ^ n := by exact_mod_cast hc.symm
  rw [← norm_pow, ← map_pow f, e, map_mul, norm_mul, hc1, one_mul, map_pow, norm_pow]

include hgen hlt in

theorem norm_pow_eq {x : K} (hx : x ≠ 0) :
    ‖f x‖ ^ h = ‖f (ϖ : K)‖ ^ (-WithZero.log (𝔭.valuation K x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, hva, hna⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt ha0
  obtain ⟨m, hvb, hnb⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt hb0
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hgen
    exact (pow_ne_zero h 𝔭.ne_bot) hgen
  have hfϖ : ‖f (ϖ : K)‖ ≠ 0 := by simpa using hϖ
  have hva' : 𝔭.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-(n : ℤ)) := by
    rw [← hva]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 a
  have hvb' : 𝔭.valuation K (algebraMap (𝓞 K) K b) = WithZero.exp (-(m : ℤ)) := by
    rw [← hvb]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 b
  rw [(𝔭.valuation K).map_div, hva', hvb', ← WithZero.exp_sub, WithZero.log_exp, map_div₀, norm_div,
    div_pow]
  change ‖f (a : K)‖ ^ h / ‖f (b : K)‖ ^ h = _
  rw [hna, hnb, show -(-(n : ℤ) - -(m : ℤ)) = (n : ℤ) - m by ring, zpow_sub₀ hfϖ, zpow_natCast,
    zpow_natCast]

end Val

end Formalism.L2.Ker.KS

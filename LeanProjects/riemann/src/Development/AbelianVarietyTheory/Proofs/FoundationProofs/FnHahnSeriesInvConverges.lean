import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSerStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_inv_converges : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  intro Ω _ ε C φ h hD hne hS
  obtain ⟨N, n₀, a, hN, ha0, hcoef, hzero⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD hne
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set p : PowerSeries Ω := PowerSeries.mk a with hpdef
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by simpa [p] using ha0
  set q : PowerSeries Ω := p⁻¹ with hqdef
  have hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N := by
    intro r m k
    rw [sub_eq_iff_eq_add]
    push_cast
    constructor <;> intro hr <;> rw [hr] <;> ring
  have hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p := by
    ext r
    rw [HahnSeries.coeff_single_mul, one_mul]
    by_cases hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]
      simp [p]
    · push_neg at hr
      rw [hzero r hr, hΦ0]
      intro k hk
      exact hr k ((hdiv r n₀ k).1 hk)
  set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef
  have hg : h⁻¹ = g := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef,
      PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]
    have : (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0 := by push_cast; ring
    rw [this, HahnSeries.single_zero_one]
  have hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q := by
    intro k
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]
  have hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0 := by
    intro r hr
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul]
    apply hΦ0
    intro k hk
    exact hr k ((hdiv r (-n₀) k).1 hk)
  refine ⟨?_, ?_⟩
  · rw [hg]
    refine ⟨N, hN, fun r hr => ?_⟩
    by_contra H
    push_neg at H
    exact hr (hgz r fun k hk => H _ hk)

  set A : ℕ → ℂ := fun k => ε (a k) with hAdef
  have hA0 : A 0 ≠ 0 := (map_ne_zero ε).2 ha0
  have hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    have hNc : ((N : ℂ)) = ((N : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc, Complex.div_ofReal_re]
    simp
    ring
  have hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := by
    intro z hz
    exact (GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)
  set t0 : ℝ := max C 0 + 1 with ht0
  set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0
  have hz0im : C < z0.im := by
    simp [z0, t0]
    have := le_max_left C 0
    linarith
  set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hsum0 := hred z0 hz0im
  have hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n := fun x hx =>
    summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx
  obtain ⟨ρ', hρ', hmain⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent A ‖x0‖ hx0pos hA0 hconv
  have hmk : PowerSeries.mk A = PowerSeries.map ε p := by
    ext k
    simp [p, A]
  have hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · rw [hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]
    · simpa using hA0
  refine ⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hx : ‖x‖ < ρ' := by
    rw [hxdef, hnorm, ← Real.exp_log hρ']
    apply Real.exp_lt_exp.2
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hpi] at hzL
    have h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N := by
      rw [lt_div_iff₀ hNr]; linarith
    have h2 := neg_abs_le (Real.log ρ')
    have h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N) := rfl
    linarith
  obtain ⟨hS0, hinv⟩ := hmain x hx
  have htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)) :=
    (hred z hzC).tsum_eq
  rw [hg]
  apply (GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2
  convert hinv using 1
  · funext k
    rw [← hmapinv, PowerSeries.coeff_map]
  · rw [htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]
    congr 2
    push_cast
    ring

end GlobalTheory

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem RestInnerTsumBound.hypotheses_inhabited_signs :
    (2 : ℝ) ≤ 3 ∧ 1 ≤ 2 ∧ ∀ n : ℕ, |(fun n : ℕ => ((-1 : ℝ) ^ n)) n| ≤ 1 := by
  refine ⟨by norm_num, by norm_num, fun n => ?_⟩
  simp [abs_pow]

def inhQ : ℕ → Fin 1 → RootRing 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0

theorem flagIntegral_second_root : flagIntegral 1 (1 + 1) flagTwoSecondRoot = -1 := by
  have h := inh_J_eq
  have hH : smallBlockMu 1 1 1 .last ^ (1 * (1 * 1)) * fibreClass 1 1 1 .last = flagTwoSecondRoot := by
    simp [inh_mu_eq, inh_fib_eq]
  rwa [fibreDegree, hH] at h

theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem inh_smallPowerSum_one (τ : Fin 1) : smallPowerSum 1 1 1 .last 1 τ = flagTwoSecondRoot := by
  fin_cases τ
  simp [smallPowerSum, yRoot, yIndex, SmallBlock.sign]

theorem inh_restTerm (τ τ' : Fin 1) :
    restTerm 1 (1 + 1) inhQ 2 τ (smallPowerSum 1 1 1 .last (2 - 1) τ') = -1 := by
  have hQ : inhQ 2 τ = C (2⁻¹) := by simp [inhQ]
  rw [show (2 : ℕ) - 1 = 1 from rfl, inh_smallPowerSum_one, restTerm, hQ, mul_comm flagTwoSecondRoot,
    flagIntegral_C_mul, flagIntegral_second_root]
  norm_num

theorem RestPrimeBoundOfFactor.hypotheses_inhabited_by_decomposition :
    IsPowerSumDecomposition 1 (1 + 1) (restPolynomial 1 1 1 .last) inhQ ∧
    restTerm 1 (1 + 1) inhQ 2 0 (smallPowerSum 1 1 1 .last (2 - 1) 0) ≠ 0 ∧
    ∀ k : ℕ, 2 ≤ k → k ≤ 1 + 1 → ∀ τ τ' : Fin 1,
        |restTerm 1 (1 + 1) inhQ k τ (smallPowerSum 1 1 1 .last (k - 1) τ')| ≤
          ((1 * (1 * 1) + 1 : ℕ) : ℚ) * |fibreDegree 1 1 1 .last| * restX 1 1 ^ (k - 1) /
            (k.factorial : ℚ) := by
  refine ⟨inh_decomp, by rw [inh_restTerm]; norm_num, ?_⟩
  intro k hk2 hk τ τ'
  obtain rfl : k = 2 := by omega
  rw [inh_restTerm, inh_J_eq]
  norm_num [restX, Nat.factorial_two]

theorem RestBoundOfPrimeBound.hypotheses_inhabited_by_decomposition
    (s : ℕ → ℕ → Fin 1 → Fin 1) (e : ℕ → ℕ → Fin 1 → ℕ → ℚ)
    (he : ∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
    ∀ p : ℕ, p.Prime → (16 : ℝ) < p →
      |restPrimeModel 1 1 1 .last inhQ s e p| ≤
        1.5 * ((1 : ℕ) : ℝ) * (restX 1 1 : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((1 * (1 * 1) + 1 : ℕ) : ℝ) * |(fibreDegree 1 1 1 .last : ℝ)| := by
  refine ⟨by norm_num, ?_⟩
  intro p hp _
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hI : Finset.Icc 2 (1 + 1) = ({2} : Finset ℕ) := by decide
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ *
      ((e p (n + 1) 0 2 * restTerm 1 (1 + 1) inhQ 2 0
        (smallPowerSum 1 1 1 .last (2 - 1) (s p (n + 1) 0)) : ℚ) : ℝ) =
      ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ)) := by
    intro n
    rw [inh_restTerm]
    push_cast
    ring
  have hnorm : ∀ n : ℕ, ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ =
      ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by
    intro n
    have h1 : |(e p (n + 1) 0 2 : ℝ)| = 1 := by
      rcases he p (n + 1) 0 2 with h | h <;> simp [h]
    have hpos : (0 : ℝ) < ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_neg, h1, mul_one, abs_of_pos hpos]
  obtain ⟨hs, hle⟩ := GeometricTail.intersectionNumber_baseChange (p : ℝ) 2 hp2 (by norm_num)
  have hs' : Summable
      (fun n : ℕ => ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖) := by
    simp_rw [hnorm]
    exact hs
  have hS : |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))| ≤
      2 * ((p : ℝ) ^ 2)⁻¹ := by
    calc |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))|
        = ‖∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' n : ℕ, ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ :=
          norm_tsum_le_tsum_norm hs'
      _ = ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by simp_rw [hnorm]
      _ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := hle
  have hmodel : restPrimeModel 1 1 1 .last inhQ s e p =
      Real.log p * ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ)) := by
    rw [restPrimeModel, hI, Fin.sum_univ_one, Finset.sum_singleton]
    simp_rw [hterm]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hX : (restX 1 1 : ℝ) = 6 := by norm_num [restX]
  have ht : 0 ≤ Real.log p * ((p : ℝ) ^ 2)⁻¹ := by positivity
  rw [hmodel, abs_mul, abs_of_nonneg hlog, hX, inh_J_eq]
  calc Real.log p * |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))|
      ≤ Real.log p * (2 * ((p : ℝ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hS hlog
    _ = 2 * (Real.log p * ((p : ℝ) ^ 2)⁻¹) := by ring
    _ ≤ 18 * (Real.log p * ((p : ℝ) ^ 2)⁻¹) := by linarith
    _ = 1.5 * ((1 : ℕ) : ℝ) * 6 * (Real.log p / (p : ℝ) ^ 2) *
          ((1 * (1 * 1) + 1 : ℕ) : ℝ) * |((-1 : ℚ) : ℝ)| := by
      rw [div_eq_mul_inv]
      norm_num
      ring

end

end RestTerms

end GroundTheory.Heights₂.Heights

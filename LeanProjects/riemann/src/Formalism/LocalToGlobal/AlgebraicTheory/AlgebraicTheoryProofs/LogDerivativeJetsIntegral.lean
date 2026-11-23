import Formalism.LocalToGlobal.AlgebraicTheory.StatementA

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

theorem jet_succ_eq {K : Type} [Field K] [CharZero K] (F a : PowerSeries K)
    (h : PowerSeries.derivative K F = a * F) (i : ℕ) :
    (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, ((i.choose p.1 : ℕ) : K) *
        ((((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a) *
        ((((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F) := by
  have h1 := congrArg (PowerSeries.coeff i) h
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h1
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i,
      ((i.choose p.1 : ℕ) : K) * (((p.1).factorial : ℕ) : K) * (((p.2).factorial : ℕ) : K) =
        ((i.factorial : ℕ) : K) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h2 : p.2 = i - p.1 := by omega
    rw [h2]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : p.1 ≤ i)
  calc (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F
      = ((i.factorial : ℕ) : K) * (PowerSeries.coeff (i + 1) F * ((i : K) + 1)) := by
        rw [Nat.factorial_succ]; push_cast; ring
    _ = ((i.factorial : ℕ) : K) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F := by rw [h1]
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          ((i.factorial : ℕ) : K) * (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F) := by
        rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [← key p hp]
        ring

theorem log_derivative_jets_integral : LogDerJets := by
  intro K _ _ _ F a ρ hρ h hF0 ha i
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
    | succ i =>
      rw [jet_succ_eq F a h i]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hq : p.2 < i + 1 := by omega
      rw [norm_mul, norm_mul]
      have h1 : ‖((i.choose p.1 : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
      have h2 := ha p.1
      have h3 := ih p.2 hq
      calc ‖((i.choose p.1 : ℕ) : K)‖ * ‖(((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a‖ *
            ‖(((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F‖
          ≤ 1 * ρ * ρ ^ p.2 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
              (mul_nonneg zero_le_one hρ0)
        _ = ρ ^ (p.2 + 1) := by ring
        _ ≤ ρ ^ (i + 1) := pow_le_pow_right₀ hρ (by omega)

theorem power_log_derivative_jets : PowLogDer := by
  intro K _ _ G V c M hM hc h
  cases M with
  | zero => omega
  | succ n =>
    have hd := congrArg (PowerSeries.derivative K) h
    rw [Derivation.leibniz_pow, Derivation.leibniz, PowerSeries.derivative_C] at hd
    simp only [smul_eq_mul, nsmul_eq_mul, smul_zero, add_zero, add_tsub_cancel_right] at hd
    have hC : (PowerSeries.C (c ^ (n + 1)) : PowerSeries K) ≠ 0 := by
      intro h0
      apply pow_ne_zero (n + 1) hc
      simpa using congrArg PowerSeries.constantCoeff h0
    apply mul_left_cancel₀ hC
    rw [map_natCast]
    linear_combination (-((n + 1 : ℕ) : PowerSeries K) * PowerSeries.derivative K G) * h + G * hd

end Formalism.L2.AlgTh

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiB
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszAPOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.ExcTerm

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

def cAP (M b n : ℕ) : ℝ := if n ≡ b [MOD M] then Λ n else 0

theorem vonMangoldtAP_nonneg (M b n : ℕ) : 0 ≤ cAP M b n := by
  unfold cAP
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl _

theorem vonMangoldtAP_le (M b n : ℕ) : cAP M b n ≤ Λ n := by
  unfold cAP
  split_ifs
  · exact le_refl _
  · exact vonMangoldt_nonneg

theorem sum_cAP (M b : ℕ) (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, cAP M b n = psiAP M b t := by
  unfold cAP Formalism.ZeroFreeDirichlet.psiAP
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨Nat.zero_le _, hx.1.2⟩, hx.2⟩
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hnx
    have hx0 : x = 0 := by
      by_contra h
      exact hnx ⟨⟨Nat.pos_of_ne_zero h, hx.1.2⟩, hx.2⟩
    subst hx0
    simp

theorem abs_piAP_sub_le (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(piAP X M b : ℝ) - ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * cAP M b n| ≤ 4 * √X * Real.log X := by
  have hpi : (piAP X M b : ℝ) = ∑ n ∈ Icc 0 ⌊X⌋₊, (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) := by
    unfold piAP
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn'
    have : n = 0 := by
      rw [Finset.mem_Icc] at hn hn'
      omega
    subst this
    simp [Nat.not_prime_zero]
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ n : ℕ, 0 ≤ (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ∧
      (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ≤
        2 * (if ¬ n.Prime then Λ n else 0) := by
    intro n
    by_cases hp : n.Prime
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      by_cases hm : n % M = b % M
      · have hm' : n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm', vonMangoldt_apply_prime hp, hlog]
      · have hm' : ¬ n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm']
    · simp only [hp, false_and, if_false, sub_zero, not_false_eq_true, if_true]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h0 : Λ n = 0 := by
          interval_cases n <;> simp
        have h0' : cAP M b n = 0 := le_antisymm (h0 ▸ vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n)
        simp [h0, h0']
      · have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        have hpos : 0 < Real.log n := by linarith
        have hinv : (Real.log n)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        constructor
        · exact mul_nonneg (inv_nonneg.2 hpos.le) (vonMangoldtAP_nonneg M b n)
        · exact mul_le_mul hinv (vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n) (by norm_num)
  have hsum : ∑ n ∈ Icc 0 ⌊X⌋₊, (if ¬ n.Prime then Λ n else 0) = Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.2 ⟨by omega, hn.2⟩
    · intro n hn hn'
      have : n = 0 := by
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc] at hn'
        omega
      subst this
      simp
  have hpt := Chebyshev.psi_sub_theta_le hX
  rw [hpi, abs_sub_comm, ← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg fun n _ => (hterm n).1)]
  calc _ ≤ ∑ n ∈ Icc 0 ⌊X⌋₊, 2 * (if ¬ n.Prime then Λ n else 0) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = 2 * (Chebyshev.psi X - Chebyshev.theta X) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith

theorem abs_psiAP_sub_le (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have hid := chebyshev_progression_orthogonality M b hb t
  have h1 : (((M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * (psiChi χ t - mainPsi e χ t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hid, hmain]
    push_cast
    ring
  have h2 : |(M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β)| ≤
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ ((b : ZMod M)⁻¹)‖ * ‖psiChi χ t - mainPsi e χ t‖ ≤ 1 * ‖psiChi χ t - mainPsi e χ t‖ := by
          gcongr
          exact χ.norm_le_one _
      _ = _ := one_mul _
  rw [le_div_iff₀ hφ]
  have h3 : (psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ) =
      (M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) := by
    unfold Fm
    field_simp
  calc |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| * (M.totient : ℝ)
      = |(psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ)| := by
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ _ := by rw [h3]; exact h2

theorem mainPsi_sum_none (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by
  have hu : IsUnit ((b : ZMod M)⁻¹) := by
    have h1 : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr hb
    obtain ⟨u, hu⟩ := h1
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  simp only [mainPsi]
  simp [Finset.sum_ite_eq', MulChar.one_apply hu]

theorem mainPsi_sum_some (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by
  have hbu : (b : ZMod M) * (b : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hb
  have hunit : IsUnit ((b : ZMod M)⁻¹) :=
    ⟨⟨(b : ZMod M)⁻¹, (b : ZMod M), by rw [mul_comm]; exact hbu, hbu⟩, rfl⟩
  have h1 : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) = 1 := MulChar.one_apply hunit
  have h2 : χ₁ ((b : ZMod M)⁻¹) = χ₁ (b : ZMod M) := by
    have h3 := congrArg χ₁ hbu
    rw [map_mul, map_one] at h3
    rcases hχ with h | h
    · rw [h, one_mul] at h3
      rw [h3, h]
    · rw [h] at h3 ⊢
      linear_combination -h3
  have hre : ((χ₁ (b : ZMod M)).re : ℂ) = χ₁ (b : ZMod M) := by
    rcases hχ with h | h <;> simp [h]
  simp only [mainPsi, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, h1, h2]
  push_cast
  rw [hre, Complex.ofReal_cpow ht]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions

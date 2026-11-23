import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChebyshevPsiProgressionRelativeErrorStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeCountRelativeErrorOfPsiRelativeErrorStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem sign_of_sq_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) (b : ℕ)
    (hb : Nat.Coprime b M) (θ : ℤ) (hθ : χ (b : ZMod M) = (θ : ℂ)) : θ = 1 ∨ θ = -1 := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have h1 : (χ ^ 2) (b : ZMod M) = 1 := by rw [h]; exact MulChar.one_apply hu
  rw [MulChar.pow_apply' χ (by norm_num), hθ] at h1
  have h2 : θ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (θ - 1) * (θ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

theorem primesRel_holds : GlobalTheory.Lin.PrimesRel := by
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  obtain ⟨a', ha', hA'⟩ := GlobalTheory.T.chebyshevPsiProgression_relative_error
  have hc₁ : 0 < min (1 / 8 : ℝ) (min a a') := lt_min (by norm_num) (lt_min ha ha')
  obtain ⟨c, hc, hE⟩ := hA _ hc₁ ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨c₂, c₃, C, h₂, h₃, hC, hP⟩ := hA' _ hc₁ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c₂', c₃', C', h₂', h₃', hC', hQ⟩ := GlobalTheory.T.primeCount_relative_error_of_psi_relative_error c₂ c₃ C c h₂ h₃ hC hc
  refine ⟨_, c₂', c₃', C', c, hc₁, min_le_left _ _, h₂', h₃', hC', hc, fun M _ hM => ?_⟩
  obtain ⟨hU, hB, -⟩ := hE M hM
  refine ⟨hU, fun χ β h => (hB χ β h).2.2.2.2, fun b θ β hb hD X hX => ?_⟩
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hφ1 : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ2 : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hθ : θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ c / (M : ℝ) ^ 3 ≤ 1 - β) := by
    rcases hD with h | ⟨χ, hχ, hb'⟩
    · exact Or.inl h.1
    · obtain ⟨-, h78, -, -, hS⟩ := hB χ β hχ
      refine Or.inr ⟨sign_of_sq_eq_one χ hχ.1 b hb θ hb', h78, le_trans ?_ hS⟩
      have hl : 0 < Real.log M := Real.log_pos (by linarith)
      have hl2 : Real.log M ≤ M := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      calc (M : ℝ) ^ 2 * Real.log M ≤ (M : ℝ) ^ 2 * M := by gcongr
        _ = (M : ℝ) ^ 3 := by ring
  have := hQ M M.totient β θ (fun n => n ≡ b [MOD M]) hM3 hφ1 hφ2 hθ
    (fun u hu => by
      have := hP M b θ β u hM hb hD hu
      unfold psiAP at this
      convert this) X hX
  convert this

end GlobalTheory.Lin

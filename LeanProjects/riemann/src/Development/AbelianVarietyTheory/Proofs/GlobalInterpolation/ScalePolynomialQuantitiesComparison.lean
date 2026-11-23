import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem _root_.GlobalTheory.scale_poly_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : _root_.Formalism.BasicNotions.Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  intro eps c κ heps hκ
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 8) c 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) c 0 κ 0 le_rfl
    (by positivity) hκ
  obtain ⟨x3, h3⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (c + 3) 1 κ 0
    (by positivity) (by linarith) hκ
  obtain ⟨x4, h4⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) (c + 1) 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x5, h5⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 3) |c| |c| κ 2
    (by positivity) (by linarith) hκ
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, ?_⟩
  intro s hs hx
  subst hs
  have ht : 1 < s.x := s.one_lt_alt
  have ht0 : 0 < s.x := by linarith
  have hlog : 0 ≤ Real.log s.x := Real.log_nonneg ht.le
  have g1 := h1 s.x (le_trans (by simp) hx)
  have g2 := h2 s.x (le_trans (by simp) hx)
  have g3 := h3 s.x (le_trans (by simp) hx)
  have g4 := h4 s.x (le_trans (by simp) hx)
  have g5 := h5 s.x (le_trans (by simp) hx)
  simp only [Real.rpow_zero, pow_zero, mul_one, zero_mul, add_zero, one_mul] at g1 g2 g3 g4
  have hxc : s.x ^ c = Real.exp (Real.log s.x * c) := Real.rpow_def_of_pos ht0 c
  have hX' : s.X' = Real.exp (s.x ^ (s.eps / 3)) := by unfold _root_.Formalism.BasicNotions.Scale.X'; rfl
  have hb : s.b = Real.exp (s.x ^ s.eps) := by unfold _root_.Formalism.BasicNotions.Scale.b _root_.Formalism.BasicNotions.Scale.L; rfl
  have hb'def : s.b' = s.x * s.b / s.X' := by unfold _root_.Formalism.BasicNotions.Scale.b' _root_.Formalism.BasicNotions.Scale.a; rfl
  have hb' : s.b' = Real.exp (Real.log s.x + s.x ^ s.eps - s.x ^ (s.eps / 3)) := by
    rw [hb'def, hb, hX', Real.exp_sub, Real.exp_add, Real.exp_log ht0]
  have hw : ∀ n : ℕ, s.w'' n = s.b' / (s.x * n) := fun n => by unfold _root_.Formalism.BasicNotions.Scale.w''; rfl
  have hX'' : ∀ n : ℕ, s.X'' n = s.x * s.b / s.w'' n := fun n => by
    unfold _root_.Formalism.BasicNotions.Scale.X'' _root_.Formalism.BasicNotions.Scale.a; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxc]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', ← Real.exp_mul]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', hb, ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb', hxc, hb, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb, ← Real.exp_mul, hxc, ← Real.exp_add, hb']
    exact Real.exp_le_exp.2 (by nlinarith)
  · intro n hn hnx
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, le_div_iff₀ (by positivity), hb, ← Real.exp_mul, hxc]
      calc Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) * (s.x * n)
          ≤ Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) *
              (s.x * s.x ^ (3 : ℝ)) := by gcongr
        _ = Real.exp (s.x ^ s.eps * (1 - κ) + Real.log s.x * c +
              (Real.log s.x + Real.log s.x * 3)) := by
            rw [Real.rpow_def_of_pos ht0 3, Real.exp_add, Real.exp_add, Real.exp_add,
              Real.exp_log ht0]
        _ ≤ s.b' := by
            rw [hb']
            exact Real.exp_le_exp.2 (by nlinarith)
    · rw [hw]
      have hpos : 0 ≤ s.b' := by rw [hb']; positivity
      exact div_le_self hpos (one_le_mul_of_one_le_of_one_le ht.le hn')
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hbne : s.b ≠ 0 := by rw [hb]; positivity
      have hX'ne : s.X' ≠ 0 := by rw [hX']; positivity
      rw [hX'', hw, hb'def]
      field_simp
  · have hY : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by positivity
    have hA : c * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
        |c| * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hY
    have hB : c * Real.log s.x ≤ |c| * Real.log s.x :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hlog
    have habs : 0 ≤ |c| := abs_nonneg c
    rw [hxc, hX', ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory

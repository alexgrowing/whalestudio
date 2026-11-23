import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem m_pow_five_mul_f_mul_L_le (s : Scale) (R : Ranks) (h : RankVal s R) :
    (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
  have hn := h.n_le
  obtain ⟨-, ⟨-, hm⟩, -, -⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have hm2 : (R.m : ℝ) ≤ 2 * s.x ^ (1 / 2 - s.eps / 16) := by
    refine hm.trans (le_of_eq ?_)
    have hd : s.delta1 = s.x ^ (-(s.eps / 8)) := rfl
    rw [hd, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith [s.eps_lt]), ← Real.rpow_mul hx0.le]
    congr 2; ring
  have hm5 : (R.m : ℝ) ^ 5 ≤ 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
    calc (R.m : ℝ) ^ 5 ≤ (2 * s.x ^ (1 / 2 - s.eps / 16)) ^ 5 := by gcongr
      _ = 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
        rw [mul_pow, ← Real.rpow_natCast (s.x ^ (1 / 2 - s.eps / 16)), ← Real.rpow_mul hx0.le]
        congr 1
        · norm_num
        · congr 1; push_cast; ring
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
    simp only [Ranks.f]; push_cast; linarith
  have hL : s.L = s.x ^ s.eps := rfl
  have hL0 : 0 ≤ s.x ^ s.eps := by positivity
  calc (R.m : ℝ) ^ 5 * R.f * s.L
      ≤ (32 * s.x ^ (5 / 2 - 5 * s.eps / 16)) * (4 * s.x ^ (2 + 8 * s.eps + s.eps / 100)) * s.x ^ s.eps := by
        rw [hL]; gcongr
    _ = 128 * (s.x ^ (5 / 2 - 5 * s.eps / 16) * s.x ^ (2 + 8 * s.eps + s.eps / 100) * s.x ^ s.eps) := by ring
    _ ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (by norm_num)

theorem exists_injective_words : ∀ eps CG CF : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ CG → 0 ≤ CF → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → ∃ c : Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ → (Fin (R.k - 2) → Bool), Function.Injective c ∧ 0 < ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ := by
  intro eps CG CF he _ hG hF
  set K : ℝ := 2 * (2 + 256 * CG + CF) + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ (1 / eps), fun s R hs hx hR => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hb := m_pow_five_mul_f_mul_L_le s R hR
  have hk := hR.2.2.1.1
  rw [hs] at hb hk
  have hKx : K ≤ s.x ^ eps := by
    calc K = (K ^ (1 / eps)) ^ eps := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ s.x ^ eps := by gcongr
  set X : ℝ := s.x ^ (9 / 2 + 9 * eps) with hX
  have hxX : s.x ≤ X := by
    calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hkX : K * X ≤ R.k := by
    refine le_trans ?_ hk
    have : s.x ^ (9 / 2 + 10 * eps) = s.x ^ eps * X := by
      rw [hX, ← Real.rpow_add hx0]; congr 1; ring
    rw [this]; gcongr
  have hk2 : 2 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hlog : Real.log s.x ≤ X := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hA : CG * (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * CG * X := by
    calc CG * (R.m : ℝ) ^ 5 * R.f * s.L = CG * ((R.m : ℝ) ^ 5 * R.f * s.L) := by ring
      _ ≤ CG * (128 * X) := by gcongr
      _ = _ := by ring
  have hFX : Real.log s.x * CF ≤ X * CF := by gcongr
  have hkc : ((R.k - 2 : ℕ) : ℝ) = (R.k : ℝ) - 2 := by rw [Nat.cast_sub hk2]; norm_num
  have hmain : 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF ≤ ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
    calc 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF
        ≤ Real.exp 2 * Real.exp (128 * CG * X) ^ 2 * Real.exp (X * CF) := by
          rw [Real.rpow_def_of_pos hx0]; gcongr
      _ = Real.exp (2 + 256 * CG * X + X * CF) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (((R.k - 2 : ℕ) : ℝ) * Real.log 2) := by
          apply Real.exp_le_exp.2
          have h1 : 2 + 256 * CG * X + X * CF ≤ ((R.k - 2 : ℕ) : ℝ) * (1 / 2) := by
            rw [hkc]; rw [hK] at hkX; nlinarith
          refine h1.trans ?_
          gcongr
      _ = ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; rfl
  have hle := Nat.ceil_le.2 hmain
  have hcard : Fintype.card (Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊) ≤
      Fintype.card (Fin (R.k - 2) → Bool) := by
    simpa using hle
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨c, c.injective, Nat.ceil_pos.2 (by positivity)⟩

end GlobalTheory.EX

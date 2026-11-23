import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem sizes_record_at {D : D7} (L : SizeData₂ D) (h : SizesAt L) (Cs : ℝ) (hCs : 5 ≤ Cs)
    (hx : 16 ≤ L.sc.x) (j : Fin 2) :
    Real.exp (8 * L.sc.x ^ L.sc.eps) ≤ (D.host.g j : ℝ) ∧ L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧
      (D.R.f : ℝ) ≤ L.sc.x ^ Cs ∧ (D.R.m : ℝ) ≤ L.sc.x ^ Cs ∧ 100 ≤ D.R.r ∧
      (D.R.r : ℝ) ≤ L.sc.x ^ Cs ∧
      Real.exp (L.sc.x ^ (L.sc.ez / 6)) ≤ ((min D.host.q D.host.d : ℕ) : ℝ) := by
  obtain ⟨hN, -, hK, -, -, -, hQ, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (D.R.k : ℝ) ≤ L.sc.x ^ (19 / 4 : ℝ) := by
    refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh
    linarith
  have h2 : (2 : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) := by
    have e : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ L.sc.x ^ Cs := by
    calc 2 * (D.R.k : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) * L.sc.x ^ (19 / 4 : ℝ) :=
          mul_le_mul h2 hkb (by linarith) (by linarith)
      _ = L.sc.x ^ (5 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ L.sc.x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1.le hCs
  have hn : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    push_cast
    linarith
  have hf : L.sc.x ^ 2 ≤ (D.R.f : ℝ) := by
    refine hn.trans ?_
    exact_mod_cast (by unfold Ranks.f; omega : D.R.n ≤ D.R.f)
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hmk' : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hr : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by
    exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hf100 : 100 ≤ D.R.f := by
    have : (100 : ℝ) ≤ D.R.f := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hf, by linarith, by linarith, by unfold Ranks.r; omega, by linarith, ?_⟩
  · refine le_trans ?_ (hG j j).1
    have e : Real.exp (8 * L.sc.x ^ L.sc.eps) = L.sc.b ^ 8 := by
      unfold Scale.b Scale.L
      rw [← Real.exp_nat_mul]
      norm_num
    have hb : 0 < L.sc.b := Real.exp_pos _
    rw [e]
    exact pow_le_pow_left₀ hb.le (le_mul_of_one_le_left hb.le hk1) 8
  · have hq : (0 : ℝ) < D.host.q := by
      have := D.host.qd_big.1
      exact_mod_cast (by omega : 0 < D.host.q)
    have hd : (0 : ℝ) < D.host.d := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : 0 < D.host.d)
    rw [Nat.cast_min]
    refine le_min ((Real.le_log_iff_exp_le hq).1 hQ.1) ((Real.le_log_iff_exp_le hd).1 ?_)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) hQ.2.2.2.1
    have := L.sc.ez_pos
    linarith

theorem family_eventually_size_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (Cs : ℝ), 5 ≤ Cs → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (j : Fin 2), Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g j : ℝ) ∧ x ^ 2 ≤ ((Fm.D x i).R.f : ℝ) ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ Cs ∧ ((Fm.D x i).R.m : ℝ) ≤ x ^ Cs ∧ 100 ≤ (Fm.D x i).R.r ∧ ((Fm.D x i).R.r : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (Fm.ez / 6)) ≤ ((min (Fm.D x i).host.q (Fm.D x i).host.d : ℕ) : ℝ) := by
  intro eps Fm Cs hCs
  refine ⟨max 16 (Fm.x1 + 1), fun x hx i j => ?_⟩
  have h16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  have := sizes_record_at (Fm.L x i) (Fm.sizes x hx1 i) Cs hCs (by rw [Fm.L_x x i hx1]; exact h16) j
  rw [Fm.L_x x i hx1, Fm.L_eps x i, Fm.L_ez x i] at this
  exact this

end GlobalTheory

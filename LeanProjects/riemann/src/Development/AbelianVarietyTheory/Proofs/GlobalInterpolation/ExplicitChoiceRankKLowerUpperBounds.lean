import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem rank_k_ineqs_poly_wide (C w y n m k : ℝ) (hw : 0 < w) (hy : 128 * |C| + 2 ≤ y)
    (hn1 : w ^ 4 * y ^ 128 ≤ n) (hn2 : n ≤ 2 * (w ^ 4 * y ^ 129))
    (hm1 : w / y ≤ m) (hm2 : m ≤ 2 * (w / y))
    (hk1 : w ^ 9 * y ^ 160 ≤ k) (hk2 : k ≤ 2 * (w ^ 9 * y ^ 160)) :
    C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16 ≤ k ∧ k ≤ w * n * (n * (y ^ 16)⁻¹) ∧
      Real.sqrt (k / m) ≤ n * (y ^ 16)⁻¹ := by
  have hC := abs_nonneg C
  have hy2 : 2 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn1
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hR : w ^ 4 * y ^ 112 ≤ n * (y ^ 16)⁻¹ := by
    calc w ^ 4 * y ^ 112 = (w ^ 4 * y ^ 128) * (y ^ 16)⁻¹ := by field_simp
      _ ≤ n * (y ^ 16)⁻¹ := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · have h5 : 128 * |C| ≤ y ^ 4 := by
      calc 128 * |C| ≤ y := by linarith
        _ ≤ y ^ 4 := le_self_pow₀ hy1 (by norm_num)
    calc C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16
        ≤ |C| * (2 * (w / y)) ^ 5 * (2 * (2 * (w ^ 4 * y ^ 129))) * y ^ 16 * y ^ 16 := by
          gcongr
          exact le_abs_self C
      _ = (128 * |C|) * (w ^ 9 * y ^ 156) := by field_simp; ring
      _ ≤ y ^ 4 * (w ^ 9 * y ^ 156) := by gcongr
      _ = w ^ 9 * y ^ 160 := by ring
      _ ≤ k := hk1
  · have h80 : 2 ≤ y ^ 80 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    calc k ≤ 2 * (w ^ 9 * y ^ 160) := hk2
      _ ≤ y ^ 80 * (w ^ 9 * y ^ 160) := by gcongr
      _ = w * (w ^ 4 * y ^ 128) * (w ^ 4 * y ^ 112) := by ring
      _ ≤ w * n * (n * (y ^ 16)⁻¹) := by gcongr
  · have h63 : 2 ≤ y ^ 63 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    refine le_trans ?_ hR
    rw [Real.sqrt_le_left (by positivity)]
    have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
    calc k / m ≤ (2 * (w ^ 9 * y ^ 160)) / (w / y) := by gcongr
      _ = 2 * (w ^ 8 * y ^ 161) := by field_simp
      _ ≤ y ^ 63 * (w ^ 8 * y ^ 161) := by gcongr
      _ = (w ^ 4 * y ^ 112) ^ 2 := by ring

theorem rank_k_ineqs_poly (C w y n m k : ℝ) (hw : 0 < w) (hy : 128 * |C| + 2 ≤ y)
    (hn1 : w ^ 4 * y ^ 128 ≤ n) (hn2 : n ≤ 2 * (w ^ 4 * y ^ 128))
    (hm1 : w / y ≤ m) (hm2 : m ≤ 2 * (w / y))
    (hk1 : w ^ 9 * y ^ 160 ≤ k) (hk2 : k ≤ 2 * (w ^ 9 * y ^ 160)) :
    C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16 ≤ k ∧ k ≤ w * n * (n * (y ^ 16)⁻¹) ∧
      Real.sqrt (k / m) ≤ n * (y ^ 16)⁻¹ := by
  have hC := abs_nonneg C
  have hy1 : 1 ≤ y := by linarith
  refine rank_k_ineqs_poly_wide C w y n m k hw hy hn1 (hn2.trans ?_) hm1 hm2 hk1 hk2
  have h : y ^ 128 ≤ y ^ 129 := pow_le_pow_right₀ hy1 (by norm_num)
  gcongr

theorem explicitChoice_rankK_lower_upper_bounds :
    SzRow (fun C D L => (C.P.CkLow * (D.R.m : ℝ) ^ jG * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k) ∧
      ((D.R.k : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) * D.R.n * R0 L) ∧ (Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ R0 L)) := by
  intro eps he _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (eps / 16)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (128 * |C.P.CkLow| + 2))
  refine ⟨x0, fun D L hε hx hV => ?_⟩
  have hn2 : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) := by
    have h1 : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])
    linarith [hV.ranks.n_le]
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  have hy := hx0 _ hx
  rw [← hε] at hy
  have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have key : ∀ (a b : ℕ), (L.sc.x ^ ((1 : ℝ) / 2)) ^ a * (L.sc.x ^ (L.sc.eps / 16)) ^ b =
      L.sc.x ^ ((a : ℝ) / 2 + b * L.sc.eps / 16) := by
    intro a b
    rw [← Real.rpow_mul_natCast hxp.le, ← Real.rpow_mul_natCast hxp.le, ← Real.rpow_add hxp]
    congr 1; ring
  have e1 : L.sc.x ^ (2 + 8 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 128 := by
    rw [key]; congr 1; push_cast; ring
  have e1' : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) =
      (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 129 := by
    rw [key]; congr 1; push_cast; ring
  have e2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 9 * (L.sc.x ^ (L.sc.eps / 16)) ^ 160 := by
    rw [key]; congr 1; push_cast; ring
  have e3 : L.sc.x ^ L.sc.eps = (L.sc.x ^ (L.sc.eps / 16)) ^ 16 := by
    rw [← Real.rpow_mul_natCast hxp.le]; congr 1; push_cast; ring
  have e4 : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 : ℝ) / 2) / L.sc.x ^ (L.sc.eps / 16) := by
    unfold Scale.delta1
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hxp.le (by positivity), ← Real.rpow_mul hxp.le, div_eq_mul_inv (_ ^ _),
      ← Real.rpow_neg hxp.le]
    congr 2; ring
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Ranks.f; push_cast; rfl
  rw [e1] at hn1
  rw [e1'] at hn2
  rw [e2] at hk1 hk2
  rw [e4] at hm1 hm2
  have h := rank_k_ineqs_poly_wide C.P.CkLow _ _ _ _ _ (by positivity) hy hn1 hn2 hm1 hm2 hk1 hk2
  simp only [R0, jG, Scale.L, hf, Real.rpow_neg hxp.le, e3]
  exact h

end GlobalTheory.EX

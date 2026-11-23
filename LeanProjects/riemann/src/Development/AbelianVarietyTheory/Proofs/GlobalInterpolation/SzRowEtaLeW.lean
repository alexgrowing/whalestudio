import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem eta_rows_of_pow_bounds {M k m r N L S η d W : ℝ} (hM : 8 ≤ M) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hr0 : 0 ≤ r) (hr : r ≤ M) (hN : N ≤ M) (hL1 : 1 ≤ L) (hL : L ≤ M) (hS0 : 0 ≤ S) (hS : S ≤ M ^ 3)
    (he0 : 0 ≤ η) (he : η ≤ M ^ 3) (hd0 : 0 ≤ d) (hd : 1 ≤ d * M) (hW : M ^ 10 ≤ W) :
    m * (S + η) ≤ W * L ∧ N * η ≤ d * m * W ∧ η ^ 2 * r * L ≤ d * m * W ^ 2 ∧ k * S ≤ W := by
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hW1 : 1 ≤ W := le_trans (one_le_pow₀ hM1) hW
  have h9 : M ^ 9 ≤ d * m * W := by
    calc M ^ 9 = 1 * M ^ 9 := by ring
      _ ≤ (d * M) * M ^ 9 := by gcongr
      _ = d * 1 * M ^ 10 := by ring
      _ ≤ d * m * W := by gcongr
  have h45 : 2 * M ^ 4 ≤ M ^ 10 := by
    calc 2 * M ^ 4 ≤ M * M ^ 4 := by gcongr; linarith
      _ = M ^ 5 := by ring
      _ ≤ M ^ 10 := pow_le_pow_right₀ hM1 (by norm_num)
  have h4 : 0 ≤ M ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m * (S + η) ≤ M * (M ^ 3 + M ^ 3) := by gcongr
      _ = 2 * M ^ 4 := by ring
      _ ≤ W * 1 := by linarith
      _ ≤ W * L := by gcongr
  · calc N * η ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ _ := h9
  · calc η ^ 2 * r * L ≤ (M ^ 3) ^ 2 * M * M := by gcongr
      _ = M ^ 8 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ d * m * W * 1 := by linarith
      _ ≤ d * m * W * W := by gcongr
      _ = _ := by ring
  · calc k * S ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ W := by linarith

theorem szRow_eta_le_w : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  intro eps h0 h1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * (10 : ℕ)) 1 h0 one_pos
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun D L he hx hV => ?_⟩
  have h8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := hx2 L.sc D.R he hxb hV.ranks
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn0 : (0 : ℝ) < D.R.n := by exact_mod_cast hn1
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast; linarith
  have hW := ((hx1 L.sc he hxa).2.2.2.2.2.1 D.R.n hn1 hn3).1
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_mul_natCast hx0.le] at hW
  set M := L.sc.x ^ (cD + ch + 402) with hM
  have key : ∀ a : ℝ, a ≤ cD + ch + 402 → L.sc.x ^ a ≤ M := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' ha
  have hxM : L.sc.x ≤ M := by simpa using key 1 (by linarith)
  have hM8 : 8 ≤ M := h8.trans hxM
  have hrM : (D.R.r : ℝ) ≤ M := hr.trans (key _ (by linarith))
  have hkM : (D.R.k : ℝ) ≤ M := le_trans (by exact_mod_cast hkr) hrM
  have hceil : ∀ a : ℝ, 0 ≤ a → a ≤ cD + ch + 402 → (⌈L.sc.x ^ a⌉₊ : ℝ) ≤ 2 * M := by
    intro a ha ha'
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le a)
    have := key a ha'
    linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; simp [Delv]
  have hEta : L.etaSz = (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) := by
    rw [hV.eta_eq]; simp [h0v]
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn0]; exact hV.host.2.2.1
  have hdp : 0 < L.sc.x ^ (-L.sc.eps) := Real.rpow_pos_of_pos hx0 _
  refine eta_rows_of_pow_bounds hM8 hkM ?_ (hm.trans hxM) (Nat.cast_nonneg _) hrM
    (hN.trans (key _ (by linarith))) hL1 (hL.trans hxM) ?_ ?_ ?_ ?_ (hdp.le.trans hd) ?_ hW
  · have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  · rw [hSc]; positivity
  · rw [hSc]
    have := hceil cD hcD (by linarith)
    calc (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) ≤ M * (4 * (2 * M)) := by gcongr
      _ = 8 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr
      _ = M ^ 3 := by ring
  · rw [hEta]; positivity
  · rw [hEta]
    have := hceil ch hch (by linarith)
    have hmM := hm.trans hxM
    calc (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) ≤ M * (2 * (2 * M)) := by gcongr
      _ = 4 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr; linarith
      _ = M ^ 3 := by ring
  · have hLM : L.sc.x ^ L.sc.eps ≤ M := hL.trans hxM
    calc (1 : ℝ) = L.sc.x ^ (-L.sc.eps) * L.sc.x ^ L.sc.eps := by
          rw [← Real.rpow_add hx0]; simp
      _ ≤ L.de2 * M := by gcongr; exact hdp.le.trans hd

end GlobalTheory.EX

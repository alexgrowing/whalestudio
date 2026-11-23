import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lowsFar_poly {y n t N l k d : ℝ} (hy : 28 ≤ y) (hn0 : 0 ≤ n) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hl0 : 0 ≤ l)
    (hk0 : 0 ≤ k) (hd0 : 0 ≤ d) (hn : n ≤ y) (ht : t ≤ y) (hN : N ≤ y) (hl : l ≤ y) (hk : k ≤ y) (hd : d ≤ 2 * y) :
    2 * (n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * d) + t + l)) + t / 2 + 3 ≤ y ^ 7 := by
  have hy0 : 0 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have h1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ y * y ^ 2 * (y + y) * y ^ 2 := by gcongr
  have h2 : k * n ^ 2 * (k * (4 * d) + t + l) ≤ y * y ^ 2 * (y * (4 * (2 * y)) + y + y) := by gcongr
  have e1 : y * y ^ 2 * (y + y) * y ^ 2 = 2 * y ^ 6 := by ring
  have e2 : y * y ^ 2 * (y * (4 * (2 * y)) + y + y) = 8 * y ^ 5 + 2 * y ^ 4 := by ring
  have p5 : y ^ 5 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p4 : y ^ 4 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p1 : y ^ 1 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p7 : 28 * y ^ 6 ≤ y ^ 7 := by
    calc 28 * y ^ 6 ≤ y * y ^ 6 := by gcongr
      _ = y ^ 7 := by ring
  rw [pow_one] at p1
  linarith

theorem half_le_abs_node_sub_mid (b : ℝ) (i j : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    H ≤ |(b + i * (2 * H)) - (b + j * (2 * H) + 2 * H / 2)| := by
  rcases Nat.lt_or_ge j i with h | h
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith))
  · have : (i : ℝ) ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith))

theorem szRow_lowsFar : SzRow (fun C D L => (∀ τ (i j : Fin D.R.m),
    2 * L.sc.b / lStar L + (D.R.t : ℝ) / 2 + 3 ≤ |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)|)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨402, fun cD hcD => ⟨cD * 7, fun ch hch => ⟨max x1 28, fun D L he hx V τ i j => ?_⟩⟩⟩
  have hx28 : 28 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  obtain ⟨hf, -, hr, hkr, -, hLx, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ :=
    hx1 L.sc D.R he (le_trans (le_max_left _ _) hx) V.ranks
  have up : ∀ a : ℝ, a ≤ 402 → L.sc.x ^ a ≤ L.sc.x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' (le_trans ha hcD)
  have hxy : L.sc.x ≤ L.sc.x ^ cD := by simpa using up 1 (by norm_num)
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.n : ℝ) ≤ D.R.f := by
      unfold Ranks.f; exact_mod_cast (by omega)
    exact this.trans (hf.trans (up _ (by norm_num)))
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (hr.trans (up _ (by norm_num)))
  have hd : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have key := lowsFar_poly (y := L.sc.x ^ cD) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn
    (ht.trans (up _ (by norm_num))) (hN.trans (up _ (by norm_num))) (hLx.trans hxy) hk hd
  have h7 : (L.sc.x ^ cD) ^ 7 ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by simpa using hch)
  obtain ⟨-, -, ⟨b1, hb, -⟩, -⟩ := V.hc
  have hdist := half_le_abs_node_sub_mid (b1 τ : ℝ) i.1 j.1 (⌈L.sc.x ^ ch⌉₊ : ℝ) (Nat.cast_nonneg _)
  have heq : (((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ) =
      ((b1 τ : ℝ) + i.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ))) -
        ((b1 τ : ℝ) + j.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) + 2 * (⌈L.sc.x ^ ch⌉₊ : ℝ) / 2) := by
    rw [(hb τ j).2, (hb τ i).1, (hb τ j).1]
    unfold h0v
    push_cast
    ring
  rw [heq]
  refine le_trans ?_ (key.trans (h7.trans hdist))
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega)
  have hS : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, V.Del_eq]; push_cast; ring
  unfold lStar
  rw [hS]
  set Λ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * ((D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) + D.R.t + L.sc.L) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ L.sc.L := by linarith
    positivity
  have : 2 * L.sc.b / ((D.R.m : ℝ) * L.sc.b / Λ) ≤ 2 * Λ := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hΛ0 hb0.le]
  linarith

end GlobalTheory.EX

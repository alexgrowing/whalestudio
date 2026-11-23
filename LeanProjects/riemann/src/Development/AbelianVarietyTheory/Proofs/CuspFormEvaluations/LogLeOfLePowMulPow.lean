import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_le_of_le_pow_mul_pow {N g₀ g₁ d X m : ℕ} {a c P : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (h₀ : Real.log g₀ ≤ a) (h₁ : Real.log g₁ ≤ a) (hd : Real.log d ≤ P) (hX : Real.log X ≤ c)
    (hN : N ≤ (g₀ * g₁) ^ m * (d * X ^ m)) : Real.log N ≤ m * (2 * a + c) + P := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]; positivity
  have key : ∀ (x : ℕ) (t : ℝ), Real.log x ≤ t → (x : ℝ) ≤ Real.exp t := fun x t h =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 h)
  have e₀ := key _ _ h₀
  have e₁ := key _ _ h₁
  have e₂ := key _ _ hd
  have e₃ := key _ _ hX
  have hN' : (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := by exact_mod_cast hN
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hpos)]
  calc (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := hN'
    _ ≤ (Real.exp a * Real.exp a) ^ m * (Real.exp P * Real.exp c ^ m) := by gcongr
    _ = Real.exp (m * (2 * a + c) + P) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring

theorem frn_le_size_sub_one {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) :
    ((D.R.f * D.R.r * w.n : ℕ) : ℝ) ≤ w.size - 1 := by
  unfold WeightFamilies.Wt.size
  have h1 : (0 : ℝ) ≤ ∑ τ, (∑ i, (w.aP τ i : ℝ) + ∑ i, (w.aM τ i : ℝ)) := by positivity
  have h2 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h3 : (D.R.f : ℝ) * 1 * D.R.r * w.n ≤ D.R.f * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * D.R.r * w.n := by
    gcongr
  rw [Nat.cast_mul, Nat.cast_mul]
  linarith

theorem log_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hp hO hPrw hN
  have hP : 0 ≤ PO D large₂ := by
    unfold PO
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hX : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    rw [Nat.cast_add, Nat.cast_one]; exact hp.2.2.2.2.2.2.2.1
  have h := log_le_of_le_pow_mul_pow (by linarith) (by linarith) hP (hp.1 0) (hp.1 1) hO.1 hX hN
  have hs := frn_le_size_sub_one w
  have hf : 0 < D.R.f := by
    unfold Ranks.f Ranks.n; positivity
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : (1 : ℝ) ≤ ((D.R.f * D.R.r * w.n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hf hr) hn
  generalize ((D.R.f * D.R.r * w.n : ℕ) : ℝ) = m at h hs hm
  generalize w.size - 1 = s at hs ⊢
  have hs0 : 0 ≤ s := by linarith
  calc Real.log N ≤ m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + PO D large₂ := h
    _ ≤ s * (38 * large₂.sc.L) + PO D large₂ * s := by
      have a1 : m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) ≤ s * (38 * large₂.sc.L) :=
        mul_le_mul hs (by linarith) (by linarith) hs0
      have a2 : PO D large₂ ≤ PO D large₂ * s := le_mul_of_one_le_right hP (hm.trans hs)
      linarith
    _ = (38 * large₂.sc.L + PO D large₂) * s := by ring
    _ ≤ Prw * s := mul_le_mul_of_nonneg_right hPrw hs0

end GlobalTheory.RunIn

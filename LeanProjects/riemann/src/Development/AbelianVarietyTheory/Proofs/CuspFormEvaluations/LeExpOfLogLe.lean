import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.LogSupMultiple

theorem le_exp_of_log_le {x b : ℝ} (h : Real.log x ≤ b) (hx : 0 ≤ x) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with rfl | hpos
  · exact (Real.exp_pos b).le
  · exact (Real.log_le_iff_le_exp hpos).1 h

theorem log_le_of_le_exp {x b : ℝ} (h : x ≤ Real.exp b) (hx : 0 ≤ x) (hb : 0 ≤ b) : Real.log x ≤ b := by
  rcases hx.eq_or_lt with rfl | hpos
  · simpa using hb
  · exact (Real.log_le_iff_le_exp hpos).2 h

theorem supN_sum_le {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) {ι : Type}
    (s : Finset ι) (F : ι → B.Cusp j w) :
    B.supN j w σ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, B.supN j w σ (F i) :=
    Finset.le_sum_of_subadditive (B.supN j w σ) (le_of_eq ((B.supN_eq_zero j w σ 0).2 rfl))
      (B.supN_add j w σ) s F

theorem log_supN_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j), (∀ (σ : B.KO →+* ℂ) (s : B.KO) (F : B.Cusp j w) (a b : ℝ), 0 ≤ a + b → Real.log ‖σ s‖ ≤ a → Real.log (B.supN j w σ F) ≤ b → 0 ≤ b → 0 ≤ a → Real.log (B.supN j w σ (s • F)) ≤ a + b) ∧ (∀ (σ : B.KO →+* ℂ) (N : ℕ) (c : Fin N → ℕ) (F : Fin N → B.Cusp j w) (b : ℝ), 0 ≤ b → (∀ i, c i ≤ N) → (∀ i, Real.log (B.supN j w σ (F i)) ≤ b) → Real.log (B.supN j w σ (∑ i, (c i : B.KO) • F i)) ≤ 2 * Real.log N + b) ∧ ∀ b : ℝ, (∑ _σ : B.KO →+* ℂ, b) / (Fintype.card (B.KO →+* ℂ) : ℝ) = b := by
  intro D B j w
  refine ⟨?_, ?_, ?_⟩
  ·
    intro σ s F a b _ hs hF hb ha
    rw [B.supN_smul]
    have hF0 := B.supN_nonneg j w σ F
    have h1 : ‖σ s‖ ≤ Real.exp a := le_exp_of_log_le hs (norm_nonneg _)
    have h2 : B.supN j w σ F ≤ Real.exp b := le_exp_of_log_le hF hF0
    refine log_le_of_le_exp ?_ (mul_nonneg (norm_nonneg _) hF0) (add_nonneg ha hb)
    rw [Real.exp_add]
    exact mul_le_mul h1 h2 hF0 (Real.exp_pos a).le
  ·
    intro σ N c F b hb hc hF
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Fin.sum_univ_zero, (B.supN_eq_zero j w σ 0).2 rfl]
      simpa using hb
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have hsum : B.supN j w σ (∑ i, (c i : B.KO) • F i) ≤ (N : ℝ) * ((N : ℝ) * Real.exp b) :=
        calc B.supN j w σ (∑ i, (c i : B.KO) • F i)
            ≤ ∑ i, B.supN j w σ ((c i : B.KO) • F i) := supN_sum_le B j w σ _ _
          _ ≤ ∑ _i : Fin N, (N : ℝ) * Real.exp b := by
            apply Finset.sum_le_sum
            intro i _
            rw [B.supN_smul, map_natCast, Complex.norm_natCast]
            exact mul_le_mul (by exact_mod_cast hc i) (le_exp_of_log_le (hF i) (B.supN_nonneg _ _ _ _))
              (B.supN_nonneg _ _ _ _) hNpos.le
          _ = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp : Real.exp (2 * Real.log N + b) = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
        rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hNpos]
        ring
      refine log_le_of_le_exp ?_ (B.supN_nonneg _ _ _ _) ?_
      · rw [hexp]
        exact hsum
      · have := Real.log_nonneg hN1
        linarith
  ·
    intro b
    have hcard : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (B.KO →+* ℂ) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ b hcard

end GlobalTheory.LogSupMultiple

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem htCmp_of_tie (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y) (H : Ht Y) (P : T.Pts)
    (hF : ∀ c, (T.F c).FamS) (hT : HtTie A H P) (hL : LatCmp H P) : HtCmp A H := by
  obtain ⟨Cl, hCl⟩ := hL
  obtain ⟨t1, -, t3, t4, t5⟩ := hT
  choose s₀ hs₀ K hK using fun c => hF c (1 + ‖A.dir‖)
  obtain ⟨K', hK'⟩ := Finite.exists_le K
  obtain ⟨M, hM⟩ := Finite.exists_le fun c => (s₀ c)⁻¹
  set Λ : ℝ := 1 + ‖A.dir‖ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set K₀ : ℝ := max K' 0 with hK₀
  have hK0 : 0 ≤ K₀ := le_max_right _ _
  have hKK : ∀ c, K c ≤ K₀ := fun c => (hK' c).trans (le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  refine ⟨(max M 1)⁻¹, by positivity, |Cl| * Λ + 2 * K₀, fun B hB u s hu hn hs hs' hd y => ?_⟩
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (s : ℝ) ≤ 1 := hs'.trans (inv_le_one_of_one_le₀ hM1)
  have hsc : ∀ c, (s : ℝ) ≤ s₀ c := fun c =>
    hs'.trans (inv_le_of_inv_le₀ (hs₀ c) ((hM c).trans (le_max_left _ _)))
  have hsh : A.sh u s = u - (s : ℝ) • A.dir := rfl
  have hnorm : ‖A.sh u s‖ ≤ Λ := by
    rw [hsh]
    refine (norm_sub_le _ _).trans (add_le_add hn ?_)
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hs1
  have hfam := fun c => hK c (A.sh u s) hd hnorm s hs0 (hsc c)
  have hsm : ∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s) := fun c σ => (hfam c σ).1
  obtain ⟨ta, tb⟩ := t5 B hB
  have hht := tb u s hu hs hd hsm y
  rw [map_add, map_add, map_smul, ← ta y, t1 B y _ (hsm _), smul_eq_mul] at hht
  have hlB : 1 / 2 ≤ Real.log B := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log two_pos hB
    linarith
  have hls : 0 ≤ Real.log (1 / (s : ℝ)) := Real.log_nonneg (one_le_one_div hs0 hs1)
  have hdiv : Real.log (B / s) = Real.log B + Real.log (1 / (s : ℝ)) := by
    rw [div_eq_mul_one_div, Real.log_mul (by linarith) (by positivity)]
  have hE : |P.ht B (Y.compPt y) y (T.L B _ (A.sh u s)) - H.h0 (A.sh u s) y| ≤ |Cl| * Λ * Real.log B :=
    (hCl B hB _ y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (le_abs_self _) hnorm (norm_nonneg _) (abs_nonneg _)) (by linarith))
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hlo : -(K₀ * Real.log (1 / (s : ℝ))) - K₀ ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) := by
    rw [← P.mean_const (Y.compPt y) y (-(K₀ * Real.log (1 / (s : ℝ))) - K₀)]
    refine P.mean_le fun σ i => le_trans ?_ ((hfam _ σ).2.2.2 _).1.1
    have := mul_le_mul_of_nonneg_right (hKK (Y.compPt y)) hls
    linarith [hKK (Y.compPt y)]
  have hup : P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) ≤ K₀ := by
    rw [← P.mean_const (Y.compPt y) y K₀]
    exact P.mean_le fun σ i => ((hfam _ σ).2.2.2 _).1.2.trans (hKK _)
  have hKB : K₀ ≤ 2 * K₀ * Real.log B := by nlinarith
  have h1 : 0 ≤ |Cl| * Λ * Real.log (1 / (s : ℝ)) := by positivity
  have h2 : 0 ≤ K₀ * Real.log (1 / (s : ℝ)) := by positivity
  refine ⟨?_, ?_, fun hy => ?_⟩
  · rw [hht, hdiv]; nlinarith
  · rw [hht]; nlinarith
  · have hm : P.mean (Y.compPt y) y ((T.F _).ph (A.sh u s)) ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) :=
      P.mean_le fun σ i => (((hfam _ σ).2.2.2 _).2 ((t3 y).1 hy σ i)).1
    rw [hht, t4 _ y hy]; nlinarith

end GlobalTheory.Mean4O

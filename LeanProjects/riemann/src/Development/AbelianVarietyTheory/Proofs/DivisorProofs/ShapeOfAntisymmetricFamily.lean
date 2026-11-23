import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationByDiscriminantMultipleStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem shapeT_of_wallBd (D : D7) (Y : ShimX D.what₂.Tau) (Φ : ℝ → Fn Y) (hh : Fn Y) (hvol : 0 < Y.vol)
    (hanti : Antisym Φ hh) (hfl : FlagHt D.what₂.Tau Y.N hh) (hw : WallBd Φ) : ShapeT Φ hh := by
  obtain ⟨C, B₁, hC⟩ := hw
  obtain ⟨C', hC', hB⟩ := GlobalTheory.T.approximation_by_discriminant_multiple D.what₂.Tau Y.N Y.j Y.j_pos Y.j_lt
  obtain ⟨h, hh1, hh2⟩ := GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) hh
  refine ⟨C' * max C 0, max B₁ 2, fun B hBB => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hBB
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast le_trans (le_max_right _ _) hBB
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) (Φ B)
  have hlog : 0 ≤ Real.log B / B := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hev : ∀ u : Wt Y, ev u (P - MvPolynomial.C Y.vol * h) = atWt Y (Φ B) u - Y.vol * atWt Y hh u := by
    intro u
    have h1 := hP2 u
    have h2 := hh2 u
    simp only [ev] at h1 h2 ⊢
    rw [map_sub, map_mul, eval_C, h1, h2]
    rfl
  have hA : AntiL Y.j (P - MvPolynomial.C Y.vol * h) := by
    intro τ a b hab hbj
    apply MvPolynomial.funext
    intro x
    have h1 := hanti B hB2 τ a b hab hbj (fun σ i => x (σ, i))
    rw [← hev, ← hev] at h1
    rw [eval_rename, map_neg]
    exact h1
  obtain ⟨al, be, E, hE1, hE2, hE3⟩ := hB P h Y.vol (max C 0 * (Real.log B / B)) hvol
    (mul_nonneg (le_max_right _ _) hlog) hP1 hh1 hA
    (fun τ lam hd hg => by rw [hh2]; exact hfl.1 Y.j τ lam Y.j_pos Y.j_lt hd hg)
    (fun τ lam hl => by
      rw [hP2]
      refine (hC B hB1 τ lam hl).trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  refine ⟨al, be, E, hE1, ?_, fun u => ?_⟩
  · rw [mul_div_assoc, mul_assoc]
    exact hE2
  · have := hE3 u
    rw [hP2, hh2] at this
    exact this

end GlobalTheory.Mean4

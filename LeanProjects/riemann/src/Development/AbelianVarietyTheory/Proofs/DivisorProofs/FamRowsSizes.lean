import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScaleLargeThree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwoLeOfLogPos
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem famRowsSizes : ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, GlobalTheory.CoreHt.DelNat (Fm.D x i) → GlobalTheory.CoreHt.HtRowsS (Fm.L x i) Fm.CYL ∧ 8 ≤ (Fm.L x i).sc.X' ∧ 2 ≤ (Fm.L x i).sc.x ∧ (∀ u, 4 * (Fm.L x i).sc.a < (((Fm.D x i).mem u).A.T : ℝ)) ∧ ∀ u, Real.log ((((Fm.D x i).mem u).A.T : ℕ) : ℝ) ≤ max Fm.CTu 0 * (Fm.D x i).R.m * (Fm.L x i).sc.L := by
  intro eps Fm hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x1, hT⟩ := hTu
  obtain ⟨xL, hL⟩ := GlobalTheory.scale_large_three eps he
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  obtain ⟨x4, h4⟩ := flipTwoThree.pow_le_exp_rpow_for_large_x 2 eps he
  refine ⟨max (max (max x1 xL) x3) (max x4 (max 9 (Fm.x1 + 1))), fun x hx i hDel => ?_⟩
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have eL : xL ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e9 : (9 : ℝ) ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  obtain ⟨hlog, h8, h2⟩ := hL (Fm.L x i).sc hse (by rw [hsx]; exact eL)
  have hThick : ThickUp (Fm.L x i) := fun j j1 j2 τ hc => ((Fm.L x i).win_thick j j1 j2 τ hc).2
  have hrows : HtRowsS (Fm.L x i) Fm.CYL := by
    have := GlobalTheory.CoreHt.RowsOfDesign.rows_of_design (Fm.D x i) (Fm.L x i) (Fm.params x e5 i) (Fm.sizes x e5 i) hlog hDel hThick
    rwa [Fm.params_CYL x e5 i] at this
  have hm : (4 : ℝ) ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; linarith)).1
    rw [hsx] at z1
    exact le_trans (h3 x e3) z1
  have hx0 : 0 < x := by linarith
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b; exact Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have h8b : 8 * x < (Fm.L x i).sc.b := by
    have hx2 := h4 x e4
    have hbe : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      unfold Scale.b Scale.L; rw [hsx, hse]
    rw [hbe]
    nlinarith
  have hb2 : (Fm.L x i).sc.b ^ (2 : ℝ) ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  rw [Real.rpow_two] at hb2
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := by linarith
  refine ⟨hrows, h8, h2, fun u => ?_, fun u => ?_⟩
  · have hTge := (hT x e1 i).1 u
    have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by unfold Scale.a; rw [hsx]
    rw [ha]
    have : 8 * (x * (Fm.L x i).sc.b) < (Fm.L x i).sc.b ^ 2 := by
      rw [← mul_assoc, sq]; exact mul_lt_mul_of_pos_right h8b hb0
    have hxb : 0 < x * (Fm.L x i).sc.b := mul_pos hx0 hb0
    linarith
  · refine le_trans ((hT x e1 i).2 u) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0

end GlobalTheory.CoreHt

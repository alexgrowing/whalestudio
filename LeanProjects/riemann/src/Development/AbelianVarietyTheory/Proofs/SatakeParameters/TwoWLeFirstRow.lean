import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopFirstRow

theorem two_w_le_first_row : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x1 (max x2 x3), fun x hx hx1 i u j hj z hz => ?_⟩
  have hxa : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hxb : x ≥ x2 := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hxc : x ≥ x3 := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := h1 x hxa hx1 i
  obtain ⟨e1, e2, e3, -⟩ := h2 x hxb hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := h3 x hxc hx1 i j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dif_pos hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dif_pos hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

end GlobalTheory.TopFirstRow

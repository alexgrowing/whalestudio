import Formalism.SharpRestriction.Divisibility.HookProducts.LwPNonneg
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.Row4C

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Proofs.HHParts

variable {D : D7} {L : SizeData₂ D}

theorem negEe_le (C : ℝ) (h2 : Formalism.MainNotions.LocalQuadraticParts.adm11 D L C) (u : D.what₂.Word) :
    -(L.Ee u) ≤ C * D.R.m * L.B0 := by
  have ha : 0 < L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_pos (by linarith [L.sc.one_lt_alt]) (Real.exp_pos _)
  have hP : 0 ≤ (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log (∏ g ∈ L.gTypes, (g : ℝ)) := by
    apply mul_nonneg
    · apply Finset.sum_nonneg
      intro t _
      exact le_trans ha.le (L.aT_win t).1
    · rw [← Nat.cast_prod]
      rcases Nat.eq_zero_or_pos (∏ g ∈ L.gTypes, g) with h | h
      · rw [h]; simp
      · exact Real.log_nonneg (Nat.one_le_cast.mpr h)
  have hj : ∀ j ∈ SizeData₂.lifts D, -(C * L.B0) ≤ ∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w) := by
    intro j hj
    have h3 := (abs_le.mp (h2 u j hj).1).1
    linarith
  have hsum := Finset.sum_le_sum hj
  have hE : L.Ee u = ∑ j ∈ SizeData₂.lifts D, ∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w) := rfl
  rw [hE]
  rw [Finset.sum_const, SizeData₂.lifts, Nat.card_Icc, nsmul_eq_mul] at hsum
  rw [SizeData₂.lifts]
  have hm : ((D.R.m + 1 - 1 : ℕ) : ℝ) = D.R.m := by simp
  rw [hm] at hsum
  linarith

def EcHH (l : List ℝ) : ℝ := 9 * (max (l.headD 0) 5 + 3) + 2

theorem gauge_form_bound_of_uniform_size {eps : ℝ} (Fm : FamP eps) (c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (Fm.L x i).Ga + (Fm.L x i).Fo - (Fm.L x i).Ee u ≤ (Fm.L x i).sc.x ^ EcHH Fm.cOut * (Fm.L x i).sc.b := by
  obtain ⟨C, xa, hC⟩ := c2
  obtain ⟨xg, hg⟩ := Formalism.MainNotions.DIV.HookProducts.Row4.ga_pow Fm
  obtain ⟨xf, hf⟩ := Formalism.MainNotions.DIV.HookProducts.HookProductWeightBounds.fo_pow Fm
  refine ⟨max (max xa xg) (max (max xf 9) (2 + |C|)), fun x hx hx1 i u => ?_⟩
  have hxa : xa ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxg : xg ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxf : xf ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx9 : 9 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hxC : 2 + |C| ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hEe := negEe_le C (hC x hxa i) u
  have hB := Formalism.MainNotions.DIV.Proofs.const_rank_base_le_poly_fourth (D := Fm.D x i) (L := Fm.L x i) C
  have hS := Formalism.MainNotions.DIV.Proofs.szPol_le_rpow (Fm.sizes x hx1 i) (by rw [hLx]; exact hx9)
  rw [Fm.Ct_eq, hLx] at hS
  have hS1 := one_le_szPol (L := Fm.L x i)
  have hGa := hg x hxg hx1 i
  have hFo := hf x hxf hx1 i
  rw [hLx]
  unfold EcHH
  simp only [Formalism.MainNotions.FamP.cOut, List.headD_cons]
  set M := max Fm.Ct 5 + 3 with hM
  have hM0 : 0 ≤ M := by have := le_max_right Fm.Ct 5; linarith
  have hb : 0 ≤ (Fm.L x i).sc.b := (Real.exp_pos _).le
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hS4 : Formalism.MainNotions.DIV.Proofs.szPol (Fm.L x i) ^ 4 ≤ x ^ (4 * M) := by
    have e : (x ^ M) ^ (4 : ℕ) = x ^ (4 * M) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1; push_cast; ring
    rw [← e]
    exact pow_le_pow_left₀ (by linarith) hS 4
  have A1 : x ^ (4 * M + 1) ≤ x ^ (9 * M + 1) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have A2 : x ^ (4 * M) ≤ x ^ (9 * M + 1) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have e2 : x ^ (9 * M + 2) = x ^ (9 * M + 1) * x := by
    rw [show 9 * M + 2 = (9 * M + 1) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
  rw [e2]
  set P := x ^ (9 * M + 1) with hP
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hx0 _).le
  have hPb : 0 ≤ P * (Fm.L x i).sc.b := mul_nonneg hP0 hb
  have t1 : (Fm.L x i).Ga ≤ P * (Fm.L x i).sc.b := hGa.trans (mul_le_mul_of_nonneg_right A1 hb)
  have t3 : -((Fm.L x i).Ee u) ≤ |C| * (P * (Fm.L x i).sc.b) := by
    have h4 : Formalism.MainNotions.DIV.Proofs.szPol (Fm.L x i) ^ 4 ≤ P := hS4.trans A2
    have h5 : |C| * Formalism.MainNotions.DIV.Proofs.szPol (Fm.L x i) ^ 4 * (Fm.L x i).sc.b ≤ |C| * (P * (Fm.L x i).sc.b) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hb) (abs_nonneg C)
    linarith
  have h := mul_le_mul_of_nonneg_right hxC hPb
  linarith [t1, hFo, t3, h]

end Formalism.MainNotions.DIV.HookProducts.Row4C

end

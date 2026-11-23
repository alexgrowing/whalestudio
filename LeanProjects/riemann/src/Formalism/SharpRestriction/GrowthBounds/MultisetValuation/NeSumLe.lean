import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundLargePrimes

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_sum_le (s : Fin (G.P.n' v)) (r : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      r * Fl.c + (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
  have h1 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), ((Fl.c : ℝ) + (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0)) := by
    apply Finset.sum_le_sum
    intro a _
    have := ne_lamI_le Fl v s a hm hb
    by_cases hc : s ∈ Fl.TT v ∧ a = 1
    · rw [if_pos hc] at this ⊢
      exact_mod_cast this
    · rw [if_neg hc] at this ⊢
      exact_mod_cast this
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Icc (G.P.m + 2 - r) (G.P.m + 1)).card : ℝ) ≤ r := by
    rw [Nat.card_Icc]
    have : G.P.m + 1 + 1 - (G.P.m + 2 - r) ≤ r := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg Fl.c : (0 : ℝ) ≤ Fl.c)
  have h4 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0) =
      (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
    by_cases hs : s ∈ Fl.TT v
    · simp only [hs, true_and]
      rw [Finset.sum_ite_eq' (Icc (G.P.m + 2 - r) (G.P.m + 1)) 1 (fun _ => (Fl.a v s : ℝ))]
      have : (1 ∈ Icc (G.P.m + 2 - r) (G.P.m + 1)) ↔ G.P.m + 1 ≤ r := by
        rw [Finset.mem_Icc]; omega
      simp only [this]
    · simp [hs]
  rw [h4] at h1
  linarith

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def ne_CX : ℝ := Real.exp (Real.exp (34 / 3))

theorem ne_k_pos : (1 : ℝ) ≤ D.R.k := by
  have h2 := D.R.m_add_three_le_k
  have : 1 ≤ D.R.k := by omega
  exact_mod_cast this

theorem ne_X' (hS : Formalism.MainNotions.SizesAt L) (hk : D.R.k ≤ Formalism.MainNotions.G.rG L.sc) : L.sc.X' ≤ ne_CX := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h4 : L.sc.x * L.sc.eps ≤ 34 := by
    have h5 : L.sc.x ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 he.le
    have h7 : (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps = 8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps := by
      field_simp
    rw [h7] at h6
    unfold Formalism.MainNotions.G.hG at h6
    linarith
  unfold Scale.X' ne_CX
  apply Real.exp_le_exp.2
  rw [Real.rpow_def_of_pos L.sc.x_pos]
  apply Real.exp_le_exp.2
  have h8 : Real.log L.sc.x ≤ L.sc.x := by
    have := Real.log_le_sub_one_of_pos L.sc.x_pos
    linarith
  have h9 := mul_le_mul_of_nonneg_right h8 (by linarith : (0 : ℝ) ≤ L.sc.eps / 3)
  linarith

theorem ne_bT_le (hS : Formalism.MainNotions.SizesAt L) (t) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hLa := hS.2.2.2.2.2.2.2.2.1
  have hRho := hS.2.2.2.2.2.2.2.2.2.1
  have hBot := hS.2.2.2.2.2.2.2.2.2.2.1 t
  unfold Formalism.MainNotions.SizeRho at hRho
  have hk := ne_k_pos (D := D)
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg L.sc.x_pos.le _) hLa.1
  have h1 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg L.sc.x_pos.le _) (Real.log_nonneg hx.le)) hLa0) (by linarith)
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h3 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h5 := mul_le_mul_of_nonneg_right h3 L.sc.b'_pos.le
  linarith

theorem ne_aT_le (t) : (L.aT t : ℝ) ≤ 2 * L.sc.a := by
  have h1 := (L.aT_win t).2
  have hk := ne_k_pos (D := D)
  have hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self L.sc.a_pos.le (by nlinarith)
  linarith

theorem ne_a_eq : L.sc.a = L.sc.X' * L.sc.b' := by
  unfold Scale.b'
  have : L.sc.X' ≠ 0 := (lt_of_lt_of_le one_pos L.sc.one_le_X').ne'
  field_simp

end Formalism.MainNotions.FormalGroupSystem.Pf

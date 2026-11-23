import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.WtTieOf

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem wG_succ_eq_shift (R : Ranks) (z : ℤ) (j : ℕ) :
    Formalism.BasicNotions.wG R (z : ℚ) (j + 1) = ((z - ((j * (R.t + 1) / 2 : ℕ) : ℤ) - ((R.N (j + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  have h1 : j * (R.t + 1) / 2 = j * (b + 1) := by
    rw [hb, show j * (2 * b + 1 + 1) = 2 * (j * (b + 1)) by ring]; omega
  have h2 : R.N (j + 1) / 2 = a + (j + 1) * (b + 1) := by
    show (R.k + (j + 1) * (R.t + 1)) / 2 = _
    rw [hb, ha, show a + a + (j + 1) * (2 * b + 1 + 1) = 2 * (a + (j + 1) * (b + 1)) by ring]; omega
  rw [h1, h2]
  unfold Formalism.BasicNotions.wG
  rw [ha, hb]
  push_cast
  ring

set_option maxHeartbeats 4000000 in

theorem fillAt_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c
  have hj' : j + 1 ≤ D.R.m := hj
  have c' : Lv.comp (j + 1) := c
  have hW := (H.core j hj' ((I.at' j hj').st.eC.symm c').1).wt
  rw [J.pos j hj'] at hW
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hk := hT.gat_k u w hg
  have rk := rk_of hT w hg (Gl.Fl u w hg) ht j
  intro e he v s
  show (Gl.Fl u w hg).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((Gl.Fl u w hg).t + 1) / 2 : ℕ) : ℤ) -
      (((((Gl.Fl u w hg).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)
  have hlt : (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < ((Gl.Fl u w hg).Pj (j + 1)).m + 1 := by
    show _ < (D.gat u w hg).P.m + (j + 1) * ((Gl.Fl u w hg).t + 1) + 1
    nlinarith
  have h := hW v s ⟨_, hlt⟩
  have h0 := (congrArg (fun z : ℤ => (z : ℚ)) h).trans (((I.at' j hj').M).lam_eq (j + 1) hj' (hT.gat_pos u w hg ⟨v, s⟩) _)
  have hi : ¬ (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < D.R.k := by omega
  have hq : ((D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) - D.R.k) / (D.R.t + 1) = j := by
    rw [← hk, ← ht, Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [finCongr_apply, Fin.coe_cast] at h0
  rw [dif_neg hi] at h0
  simp only [hq] at h0
  have hL : ((Gl.Fl u w hg).Pj (j + 1)).lam0 v s ⟨_, hlt⟩ = -((Gl.Fl u w hg).w v (j + 1) s) := by
    show liftWt (Gl.Fl u w hg).t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => (Gl.Fl u w hg).w v a s) (j + 1) ⟨_, hlt⟩ = _
    unfold liftWt
    rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))]
    congr 2
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel _ (Nat.succ_pos _)]
  rw [hL, Int.cast_neg, neg_inj, D.hcW_e, ← he] at h0
  rw [rk, ht]
  apply Int.cast_injective (α := ℚ)
  rw [h0]
  exact wG_succ_eq_shift D.R _ j

end GlobalTheory.TwV.Xc

end

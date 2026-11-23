import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

variable {eps : ℝ} (Fm : FamP eps)

theorem eps_pos (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i0).sc.eps_pos
  rwa [Fm.L_eps] at h

theorem eps_lt (Fm : FamP eps) : eps < 1 / 52 := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i0).sc.eps_lt
  rwa [Fm.L_eps] at h

theorem sc_L {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.L x i).sc.L = x ^ eps := by
  rw [Formalism.BasicNotions.Scale.L, Fm.L_x x i hx, Fm.L_eps]

theorem one_lt_of {x : ℝ} (hx : Fm.x1 < x) : 1 < x := by
  exact lt_trans Fm.one_lt_family_threshold hx

theorem ev_rpow {c : ℝ} (hc : 0 < c) (K : ℝ) : ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, K ≤ x ^ c := by
  refine ⟨max 2 (|K| ^ c⁻¹), by linarith [le_max_left 2 (|K| ^ c⁻¹)], fun x hx => ?_⟩
  have h0 : 0 ≤ |K| ^ c⁻¹ := Real.rpow_nonneg (abs_nonneg K) _
  calc K ≤ |K| := le_abs_self K
    _ = (|K| ^ c⁻¹) ^ c := (Real.rpow_inv_rpow (abs_nonneg K) hc.ne').symm
    _ ≤ x ^ c := Real.rpow_le_rpow h0 (le_trans (le_max_right _ _) hx) hc.le

theorem ev_L (K : ℝ) : ∃ x0 : ℝ, Fm.x1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, K ≤ (Fm.L x i).sc.L := by
  obtain ⟨x0, -, hx0⟩ := ev_rpow (eps_pos Fm) K
  refine ⟨max x0 (Fm.x1 + 1), by linarith [le_max_right x0 (Fm.x1 + 1)], fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith [le_max_right x0 (Fm.x1 + 1)]
  rw [sc_L Fm hx1 i]
  exact hx0 x (le_trans (le_max_left _ _) hx)

theorem m_ge {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) : x ^ ((1 : ℝ) / 4) ≤ ((Fm.D x i).R.m : ℝ) := by
  have hx1 : 1 < x := one_lt_of Fm hx
  have hx0 : 0 < x := by linarith
  have he := eps_pos Fm
  have he' := eps_lt Fm
  have hS := (Fm.sizes x hx i).2.1.1
  simp only [Formalism.MainNotions.szTh, Formalism.BasicNotions.Scale.delta1, Fm.L_x x i hx, Fm.L_eps] at hS
  refine le_trans ?_ hS
  rw [show x * x ^ (-(eps / 8)) = x ^ (1 + -(eps / 8)) by rw [Real.rpow_add hx0, Real.rpow_one],
    Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)

theorem ev_m (K : ℝ) : ∃ x0 : ℝ, Fm.x1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, K ≤ ((Fm.D x i).R.m : ℝ) := by
  obtain ⟨x0, -, hx0⟩ := ev_rpow (by norm_num : (0 : ℝ) < 1 / 4) K
  refine ⟨max x0 (Fm.x1 + 1), by linarith [le_max_right x0 (Fm.x1 + 1)], fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith [le_max_right x0 (Fm.x1 + 1)]
  exact le_trans (hx0 x (le_trans (le_max_left _ _) hx)) (m_ge Fm hx1 i)

theorem m_le_k (D : D7) : (D.R.m : ℝ) ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  exact_mod_cast (by omega : D.R.m ≤ D.R.k)

theorem ev_k (K : ℝ) : ∃ x0 : ℝ, Fm.x1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, K ≤ ((Fm.D x i).R.k : ℝ) := by
  obtain ⟨x0, hx0, h⟩ := ev_m Fm K
  exact ⟨x0, hx0, fun x hx i => le_trans (h x hx i) (m_le_k _)⟩

theorem ownEv_intro {P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop} (x0 : ℝ)
    (h : ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, P (sC' Fm) (sCl Fm) x i) : OwnEv Fm P := by
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => h x (le_trans (le_max_left _ _) hx) ?_ i⟩
  linarith [le_max_right x0 (Fm.x1 + 1)]

end Formalism.MainNotions.BridgeLemma

end

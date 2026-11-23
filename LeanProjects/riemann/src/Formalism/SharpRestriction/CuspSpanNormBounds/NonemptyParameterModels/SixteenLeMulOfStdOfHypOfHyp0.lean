import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton

noncomputable section

namespace Formalism.MainNotions.S.Inh

section a5

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

theorem tau_index_set_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  first
  | exact D.eTau.nonempty
  | exact ⟨D.eTau.symm 1⟩

theorem one_lt_scale_base (D : D7) (large₂ : SizeData₂ D) : 1 < large₂.sc.b := by
  exact Formalism.MainNotions.sc_one_lt_b large₂

theorem scale_base_pow_sixteen_le (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ)
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : large₂.sc.b ^ (16 : ℝ) ≤ (kaS D)⁻¹ := by
  have hb := Formalism.MainNotions.sc_one_lt_b large₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -⟩ := h
  have hk2 : (2 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (show 2 ≤ D.R.k by omega)
  have hpi := Real.pi_le_four
  have hpi0 := Real.pi_pos
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : (0 : ℝ) < D.host.v := by linarith
  have hc : 2 * large₂.sc.b ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h8 : (2 * large₂.sc.b) ^ 8 ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    first
    | exact pow_le_pow_left₀ (by linarith) hc 8
    | exact pow_le_pow_left (by linarith) hc 8
  have hgg := mul_le_mul hg1 hg2 (by positivity) (le_trans (by positivity) hg1)
  have e16 : large₂.sc.b ^ (16 : ℝ) = large₂.sc.b ^ (16 : ℕ) := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e16]
  unfold kaS gg
  rw [show D.host.ka = Real.pi / D.host.v from rfl, inv_div]
  have hpv : Real.pi / D.host.v ≤ 4 := le_trans (div_le_self hpi0.le hv) hpi
  have hpos : 0 < Real.pi / D.host.v := div_pos hpi0 hv0
  rw [le_div_iff₀ hpos]
  calc large₂.sc.b ^ 16 * (Real.pi / D.host.v) ≤ large₂.sc.b ^ 16 * 4 :=
        mul_le_mul_of_nonneg_left hpv (by positivity)
    _ ≤ 65536 * large₂.sc.b ^ 16 := by have := pow_pos hb0 16; linarith
    _ = (2 * large₂.sc.b) ^ 8 * (2 * large₂.sc.b) ^ 8 := by ring
    _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 * ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
        mul_le_mul h8 h8 (by positivity) (by positivity)
    _ ≤ _ := hgg

theorem sixteen_le_mul_of_stdOfHyp_of_hyp0 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ : ℝ)
    (h : StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ) (hy : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) :
    16 ≤ Cβ * Ch := by
  have hb := Formalism.MainNotions.sc_one_lt_b large₂
  have hy' := hy
  obtain ⟨hS0, -, -⟩ := hy'
  have h16 := scale_base_pow_sixteen_le D large₂ C' Cl Cg cb Cu cT CT hS0
  obtain ⟨τ⟩ := tau_index_set_nonempty D
  obtain ⟨hs, -⟩ := h hy τ D.u₀ D.u₀
  obtain ⟨-, -, -, -, -, hka, -⟩ := hs
  rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ large₂.sc.b)] at hka
  exact (Real.rpow_le_rpow_left_iff hb).mp (le_trans h16 hka)

theorem product_bound_forces_pos (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ)
    (h : ProdBound D large₂ C' Cl Cg cb Cu cT CT C0 0 C) (hy : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : 0 < C := by
  obtain ⟨τ⟩ := tau_index_set_nonempty D
  have hk := D.R.m_add_three_le_k
  have hA : StrictAnti (lamD D τ) := Formalism.MainNotions.S.Inh.amp_lamSH_strictAnti D.R (D.hc τ)
  have h0d : l1dist (lamD D τ) (lamD D τ) = 0 := by
    simp only [l1dist, sub_self, abs_zero, Finset.sum_const_zero]
  obtain ⟨-, hup⟩ := h hy τ (lamD D τ) (by rw [h0d]; norm_num) 0
  have hfac : ∀ s' ∈ (Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1))),
      1 < (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s') := by
    intro s' hs'
    have hne := (Finset.mem_erase.mp hs').1
    have hlt : (0 : Fin (2 * D.R.rS + D.R.k + 1)) < s' := by
      rw [Fin.lt_iff_val_lt_val, Fin.val_zero]
      exact Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext (by rw [h0, Fin.val_zero])))
    have hμ := hA hlt
    rw [one_lt_div (sub_pos.mpr hμ)]
    linarith
  have hlast : Fin.last (2 * D.R.rS + D.R.k) ∈
      (Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1))) := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h0
    have h1 := congrArg Fin.val h0
    rw [Fin.val_last, Fin.val_zero] at h1
    omega
  have hrest : 1 ≤ ∏ s' ∈ (Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1))).erase
      (Fin.last (2 * D.R.rS + D.R.k)),
      (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s') := by
    have := Finset.prod_le_prod
      (s := (Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1))).erase (Fin.last (2 * D.R.rS + D.R.k)))
      (f := fun _ => (1 : ℝ))
      (g := fun s' => (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s'))
      (fun _ _ => zero_le_one) (fun s' hs' => (hfac s' (Finset.mem_of_mem_erase hs')).le)
    simp only [Finset.prod_const_one] at this
    exact this
  have hprod : 1 < ∏ s' ∈ Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1)),
      (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s') := by
    have h1 := hfac _ hlast
    calc (1 : ℝ) < ((lamD D τ 0 + 1 - lamD D τ (Fin.last (2 * D.R.rS + D.R.k))) /
          (lamD D τ 0 - lamD D τ (Fin.last (2 * D.R.rS + D.R.k)))) * 1 := by rw [mul_one]; exact h1
      _ ≤ ((lamD D τ 0 + 1 - lamD D τ (Fin.last (2 * D.R.rS + D.R.k))) /
          (lamD D τ 0 - lamD D τ (Fin.last (2 * D.R.rS + D.R.k)))) *
          ∏ s' ∈ (Finset.univ.erase (0 : Fin (2 * D.R.rS + D.R.k + 1))).erase
            (Fin.last (2 * D.R.rS + D.R.k)),
            (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s') :=
          mul_le_mul_of_nonneg_left hrest (by linarith)
      _ = _ := Finset.mul_prod_erase _
          (fun s' => (lamD D τ 0 + 1 - lamD D τ s') / (lamD D τ 0 - lamD D τ s')) hlast
  by_contra hC
  push_neg at hC
  have hr1 : (D.R.r : ℝ) ^ C ≤ 1 := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | hpos
    · rw [h0, Nat.cast_zero]
      first
      | exact Real.zero_rpow_le_one C
      | (rcases eq_or_ne C 0 with hc0 | hc0
         · rw [hc0, Real.rpow_zero]
         · rw [Real.zero_rpow hc0]; norm_num)
    · exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hpos) hC
  exact absurd (lt_of_lt_of_le hprod (le_trans hup hr1)) (lt_irrefl 1)

variable {eps : ℝ}

theorem no_window_of_standard_hyp (Fm : FamP eps) (C0 Ch Cβ : ℝ) (h1 : 1 ≤ C0) (hR : ResidualStandingConditions Fm) (hs : Cβ * Ch < 16)
    (pStd : PX.StdHypS Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 Ch Cβ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ¬ Win Fm C0 x i := by
  have h0 := standing_hypotheses_hold_family (Fm := Fm) C0 h1 hR
  unfold StandingHypothesesWithConstants OwnEv at h0
  obtain ⟨x0, hx0⟩ := h0
  have h2 := pStd 0 0
  unfold OwnEv at h2
  obtain ⟨x1, hx1⟩ := h2
  refine ⟨max x0 x1, fun x hx i hw => ?_⟩
  obtain ⟨hD, hS, hc⟩ := hx0 x (le_of_max_le_left hx) i hw
  have hy0 : Cnt.Hyp0 (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
    ⟨hS, hD, hc⟩
  have h3 := sixteen_le_mul_of_stdOfHyp_of_hyp0 (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 Ch 0 0 Cβ
    (hx1 x (le_of_max_le_right hx) i) hy0
  linarith

theorem no_window_of_product_bound (Fm : FamP eps) (C0 C : ℝ) (h1 : 1 ≤ C0) (hR : ResidualStandingConditions Fm) (hs : C ≤ 0)
    (pProd : PX.PieriProductBound Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 C) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ¬ Win Fm C0 x i := by
  have h0 := standing_hypotheses_hold_family (Fm := Fm) C0 h1 hR
  unfold StandingHypothesesWithConstants OwnEv at h0
  obtain ⟨x0, hx0⟩ := h0
  have h2 := pProd 0
  unfold OwnEv at h2
  obtain ⟨x1, hx1⟩ := h2
  refine ⟨max x0 x1, fun x hx i hw => ?_⟩
  obtain ⟨hD, hS, hc⟩ := hx0 x (le_of_max_le_left hx) i hw
  have hy0 : Cnt.Hyp0 (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
    ⟨hS, hD, hc⟩
  have h3 := product_bound_forces_pos (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 C
    (hx1 x (le_of_max_le_right hx) i) hy0
  linarith

theorem level_frame_forces_rank_bound (Fm : FamP eps) (C0 : ℝ) (h1 : 1 ≤ C0) (hR : ResidualStandingConditions Fm)
    (pTF : PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Win Fm C0 x i →
      ((32 * (Fm.D x i).R.rS : ℕ) : ℝ) ≤ Fm.CTu * ((Fm.D x i).R.m : ℝ) := by
  have h0 := standing_hypotheses_hold_family (Fm := Fm) C0 h1 hR
  unfold StandingHypothesesWithConstants OwnEv at h0
  obtain ⟨x0, hx0⟩ := h0
  have h2 := pTF
  unfold OwnEv at h2
  obtain ⟨x1, hx1⟩ := h2
  have h3 := hR.2.1
  unfold TuSize at h3
  obtain ⟨x2, hx2⟩ := h3
  refine ⟨max x0 (max x1 x2), fun x hx i hw => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxb : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hD, hS, hc⟩ := hx0 x hxa i hw
  have hy0 : Cnt.Hyp0 (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
    ⟨hS, hD, hc⟩
  have hT1 := hx1 x hxb i hy0 (Fm.D x i).u₀
  have hTs := (hx2 x hxc i).2 (Fm.D x i).u₀
  have h16 := scale_base_pow_sixteen_le (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu hS
  have hTr : Tr (Fm.D x i) (Fm.D x i).u₀ = ((((Fm.D x i).mem (Fm.D x i).u₀).A.T : ℕ) : ℝ) := rfl
  rw [hTr] at hT1
  have hb0 : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hbpos : 0 < (Fm.L x i).sc.b ^ (16 : ℝ) := Real.rpow_pos_of_pos hb0 _
  have hκ : 0 < kaS (Fm.D x i) := inv_pos.mp (lt_of_lt_of_le hbpos h16)
  have hP : 0 < kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS) := pow_pos hκ _
  have hT : 0 < ((((Fm.D x i).mem (Fm.D x i).u₀).A.T : ℕ) : ℝ) := by
    by_contra hT0
    push_neg at hT0
    nlinarith
  have hlog1 := Real.log_nonneg hT1
  rw [Real.log_mul hT.ne' hP.ne', Real.log_pow] at hlog1
  have hlk : 16 * (Fm.L x i).sc.L ≤ -Real.log (kaS (Fm.D x i)) := by
    have h5 := Real.log_le_log hbpos h16
    rw [Real.log_inv, show (Fm.L x i).sc.b = Real.exp (Fm.L x i).sc.L from rfl,
      Real.log_rpow (Real.exp_pos _), Real.log_exp] at h5
    linarith
  have hL : 0 < (Fm.L x i).sc.L := Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hn : (0 : ℝ) ≤ ((Fm.D x i).R.rS : ℝ) := Nat.cast_nonneg _
  have hm6 := mul_le_mul_of_nonneg_left hlk hn
  push_cast at hlog1
  have key : 32 * ((Fm.D x i).R.rS : ℝ) * (Fm.L x i).sc.L ≤ Fm.CTu * ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L := by
    linarith
  push_cast
  have h7 := le_of_mul_le_mul_right key hL
  linarith

end a5

end Formalism.MainNotions.S.Inh

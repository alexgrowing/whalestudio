import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_exp_nd {m f s r c mx cf C : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hf : 1 ≤ f) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hmx : 0 ≤ mx) (hcf : cf ≤ m) (hC : 4 + (c ^ 2 + 2 * mx) * (6 * c + 2) ≤ C ^ 2) :
    1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by
  have hm2 : 2 ≤ m := by linarith
  set Mx : ℝ := (s + m) * m with hMx
  have hMx1 : m ^ 2 ≤ Mx := by rw [hMx]; nlinarith
  have hMx2 : m ≤ Mx := by nlinarith
  have hMx0 : 0 ≤ Mx := by nlinarith
  have hr1 : r + 1 = m / 2 := by linarith
  have hrm : r ^ 2 ≤ Mx := by nlinarith
  have e1 : c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1)) = (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by rw [hr1]; ring
  have b1 : c * cf ≤ c * Mx := mul_le_mul_of_nonneg_left (hcf.trans hMx2) hc
  have b2 : c * r ^ 2 ≤ c * Mx := mul_le_mul_of_nonneg_left hrm hc
  have b3 : 6 * (r + 1) ^ 2 ≤ 2 * Mx := by rw [hr1]; nlinarith
  have br : 2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2 ≤ (6 * c + 2) * Mx := by
    have : c * (s + m) * m = c * Mx := by rw [hMx]; ring
    rw [this]; nlinarith
  have hK0 : 0 ≤ m ^ 3 * f := by positivity
  have hp0 : 0 ≤ (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by positivity
  have t1 : (c ^ 2 + 2 * mx) * (m ^ 3 * f) * (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := mul_le_mul_of_nonneg_left br hp0
  have hKM : 0 ≤ m ^ 3 * f * Mx := by positivity
  have t2 : 1 + 12 * f * (r + 1) ^ 2 ≤ 4 * (m ^ 3 * f * Mx) := by
    rw [hr1]
    have a1 : f * m ^ 2 ≤ m ^ 3 * f * Mx := by
      have : (1 : ℝ) ≤ m * Mx := by nlinarith
      calc f * m ^ 2 = f * m ^ 2 * 1 := by ring
        _ ≤ f * m ^ 2 * (m * Mx) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = m ^ 3 * f * Mx := by ring
    have a2 : (1 : ℝ) ≤ f * m ^ 2 := by nlinarith
    nlinarith
  have t3 : (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) ≤ C ^ 2 * (m ^ 3 * f * Mx) :=
    mul_le_mul_of_nonneg_right hC hKM
  rw [e1]
  calc 1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 + 2 * mx) * (m ^ 3 * f) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2)
      ≤ 4 * (m ^ 3 * f * Mx) + (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := add_le_add t2 t1
    _ = (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) := by ring
    _ ≤ C ^ 2 * (m ^ 3 * f * Mx) := t3
    _ = C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by rw [hMx]; ring

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_m_cast (D : D7) : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by
  have := d_m_eq D; exact_mod_cast this

theorem rows_cF_le {C' Cl Cg cb Cu cT CT C0 A : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    cF D.R.f ≤ D.R.m := by
  obtain ⟨_, _, _, _, h5, _⟩ := hH.1.1
  have h5' : Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.rS : ℝ) := h5
  have hr : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hH.2.1.1
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hsq : Real.sqrt (D.R.rS : ℝ) ≤ D.R.rS := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hl2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log (D.R.f : ℝ) := Real.log_nonneg hf
  have e : cF D.R.f = 2 + Real.log (D.R.f : ℝ) / Real.log 2 := by
    unfold cF lg2f Real.logb
    rw [Real.log_mul (by norm_num) (by linarith)]
    field_simp
    ring
  have h2 : Real.log (D.R.f : ℝ) / Real.log 2 ≤ 2 * Real.log (D.R.f : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [e, rows_m_cast]
  linarith

theorem rows_one_le_NT (D : D7) (w : D.what₂.Word) : 1 ≤ NT D w := by
  unfold NT
  exact one_le_pow₀ (by exact_mod_cast (D.mem w).A.T_prime.pos)

theorem rows_XiP_le (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c Ch C : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    (hC : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) (s : ℕ) :
    XiS D w (rows_P D large₂ c Ch ^ 2) c s ≤ XiB D large₂ w C s := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hP1 := rows_P_one_le D large₂ c Ch
  have hN := rows_one_le_NT D w
  have hPH : rows_P D large₂ c Ch ^ 2 ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) := by
    unfold rows_P Hb
    rw [rows_rpow_pow hb0, ← Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  unfold XiB XiS Xi
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ rows_P D large₂ c Ch ^ 2 * NT D w := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP1) hN
    have h2 : rows_P D large₂ c Ch ^ 2 * NT D w ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w :=
      mul_le_mul_of_nonneg_right hPH (by linarith)
    have h3 : (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ)) ≤
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (C * (D.R.k : ℝ)) :=
      calc (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ))
          ≤ (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (c * (D.R.k : ℝ)) :=
            Real.rpow_le_rpow (by linarith) h2 (by positivity)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (h1.trans h2) (by gcongr)
    have h4 : (c * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) ≤ (C * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    exact mul_le_mul h4 h3 (Real.rpow_nonneg (by linarith) _) (by
      have : 0 ≤ C := hc.trans hcC
      positivity)
  · exact le_rfl

theorem rows_ndB_le {C' Cl Cg cb Cu cT CT C0 A c Ch δ C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (s : ℕ) :
    rows_ndB D large₂ u u' c Ch δ s ≤
      LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) * rDD D u' := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := gg D)
    (v := D.host.v) (Γ := GamS D large₂) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := δ) (rD := rDD D u') (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by linarith) (by linarith) hGam0.le hc hcC hC1 hδ0 hδ
    (rows_rDD_nonneg D u') (rows_XiS_nonneg D u (by positivity) hc s) (rows_XiP_le D large₂ u hc hcC hpe2 s)
    (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold rows_ndB rows_R rows_Phi
  exact this

theorem rows_RowBound_mono {Q : D.s.Pair u u' → Prop} {B B' : ℝ} (h : RowBound X Y Q B) (hB : B ≤ B')
    (hdim : 0 ≤ dimPi (hc := D.hcW) u) : RowBound X Y Q B' := fun S hS =>
  (h S hS).trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (rows_massRows_nonneg Y) hdim))

theorem rows_RowsND_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hδ : δ ≤ 1) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsND X Y C := by
  intro s hs hsk
  refine rows_RowBound_mono Y (rows_ND_record Y h s hs hsk ?_) (rows_ndB_le h.hH h.hc hcC hC1 h.hδ hδ hC s) h.hdim.le
  have : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
    have := h.hc
    gcongr
  linarith

end Rec

end Formalism.MainNotions.BridgeLemma₂

end

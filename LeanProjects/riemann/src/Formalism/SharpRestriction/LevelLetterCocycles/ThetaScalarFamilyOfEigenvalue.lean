import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.SumRepresentations
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem ev_and {eps : ℝ} (Fm : FamP eps) {P Q : ∀ x, Fm.Ix x → Prop}
    (hP : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P x i) (hQ : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Q x i) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P x i ∧ Q x i := by
  obtain ⟨x1, h1⟩ := hP
  obtain ⟨x2, h2⟩ := hQ
  exact ⟨max x1 x2, fun x hx i =>
    ⟨h1 x (le_trans (le_max_left _ _) hx) i, h2 x (le_trans (le_max_right _ _) hx) i⟩⟩

theorem logWeight_nonneg {D : D7} (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP Formalism.BasicNotions.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem etaSum_eq {D : D7} (L : SizeData₂ D) (j : ℕ) : Formalism.MainNotions.etaSum L j = Formalism.MainNotions.TwistedPlaces.etaSum L j := rfl

theorem etaSum_le {D : D7} (L : SizeData₂ D) (j : ℕ) : Formalism.MainNotions.etaSum L j ≤ Formalism.MainNotions.TwistedPlaces.etaSum L j := le_of_eq (etaSum_eq L j)

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem export_link_iff_family {eps : ℝ} (Fm : FamP eps) : LinkN Fm ↔ Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm := by
  refine ⟨fun h => ?_, export_link_of_family Fm⟩
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃
  exact fun hsha hS j hj => hp hsha j hj hS

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

theorem linkN_of_stmtU {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.UniformExportStatement eps) :
    LinkN Fm := by
  obtain ⟨Ca, hCa⟩ := hA
  obtain ⟨C, hC⟩ := hS Ca
  obtain ⟨x0, hx0⟩ := hC Fm hCa
  exact export_link_of_family Fm ⟨C, x0, hx0⟩

theorem ev_rpow (K A κ α β : ℝ) (hκ : 0 < κ) (hα : 0 < α) (hβ : β < α) :
    ∀ᶠ x : ℝ in atTop, K * x ^ A * Real.exp (-(κ * x ^ α)) ≤ Real.exp (-(x ^ β)) := by
  have hab : 0 < α - β := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, x ^ (-(α - β)) < κ / 2 :=
    (tendsto_rpow_neg_atTop hab).eventually (eventually_lt_nhds (by linarith))
  have h2 : Tendsto (fun x : ℝ => (x ^ α) ^ (A / α) * Real.exp (-(κ / 2) * x ^ α)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / α) (κ / 2) (by linarith)).comp
      (tendsto_rpow_atTop hα)
  have h3 : ∀ᶠ x : ℝ in atTop, (x ^ α) ^ (A / α) * Real.exp (-(κ / 2) * x ^ α) < 1 / (|K| + 1) :=
    h2.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [h1, h3, eventually_gt_atTop 0] with x hx1 hx3 hx0
  have hxA : (x ^ α) ^ (A / α) = x ^ A := by
    rw [← Real.rpow_mul hx0.le, mul_div_cancel₀ A hα.ne']
  rw [hxA] at hx3
  have hxb : x ^ β ≤ κ / 2 * x ^ α := by
    have : x ^ β = x ^ (-(α - β)) * x ^ α := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx1.le (Real.rpow_nonneg hx0.le α)
  have hE0 : 0 < Real.exp (-(κ / 2) * x ^ α) := Real.exp_pos _
  have hsplit : Real.exp (-(κ * x ^ α)) = Real.exp (-(κ / 2) * x ^ α) * Real.exp (-(κ / 2) * x ^ α) := by
    rw [← Real.exp_add]; congr 1; ring
  have hxA0 : 0 ≤ x ^ A := Real.rpow_nonneg hx0.le A
  have hK1 : K ≤ |K| + 1 := by have := le_abs_self K; linarith
  have hpos : 0 < |K| + 1 := by positivity
  have hK : K * x ^ A * Real.exp (-(κ / 2) * x ^ α) ≤ 1 := by
    calc K * x ^ A * Real.exp (-(κ / 2) * x ^ α)
        ≤ (|K| + 1) * (x ^ A * Real.exp (-(κ / 2) * x ^ α)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hK1 (mul_nonneg hxA0 hE0.le)
      _ ≤ (|K| + 1) * (1 / (|K| + 1)) := mul_le_mul_of_nonneg_left hx3.le hpos.le
      _ = 1 := by field_simp
  calc K * x ^ A * Real.exp (-(κ * x ^ α))
      = (K * x ^ A * Real.exp (-(κ / 2) * x ^ α)) * Real.exp (-(κ / 2) * x ^ α) := by
        rw [hsplit]; ring
    _ ≤ 1 * Real.exp (-(κ / 2) * x ^ α) := mul_le_mul_of_nonneg_right hK hE0.le
    _ = Real.exp (-(κ / 2) * x ^ α) := one_mul _
    _ ≤ Real.exp (-(x ^ β)) := Real.exp_le_exp.mpr (by linarith)

theorem ev_pow (K : ℝ) (A : ℕ) (κ α β : ℝ) (hκ : 0 < κ) (hα : 0 < α) (hβ : β < α) :
    ∀ᶠ x : ℝ in atTop, K * x ^ A * Real.exp (-(κ * x ^ α)) ≤ Real.exp (-(x ^ β)) := (ev_rpow K A κ α β hκ hα hβ).mono fun x hx => by rwa [Real.rpow_natCast] at hx

theorem exp_le_natCast (N : ℕ) (y : ℝ) (hy : 0 < y) (h : y ≤ Real.log N) : Real.exp y ≤ N := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp at h
      linarith
    · exact_mod_cast h0
  calc Real.exp y ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr h
    _ = N := Real.exp_log hN

theorem exponential_tail_fourth (x c f r : ℝ) (hx2 : 2 ≤ x) (hc : 0 < c) (hf_lo : 2 * x ^ 2 ≤ f) (hr_hi : r ≤ 2 * x ^ 5)
    (hr2 : 2 ≤ r) :
    Real.exp (-(c * f / Real.log r)) ≤ 1 * x ^ 0 * Real.exp (-(c / 3 * x ^ (1 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hlr_le : Real.log r ≤ 6 * x := by
    have h1 : Real.log r ≤ Real.log (2 * x ^ 5) := Real.log_le_log hr0 hr_hi
    have h2 : Real.log (2 * x ^ 5) = Real.log 2 + 5 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_pos hx0 5).ne', Real.log_pow]
      push_cast
      ring
    linarith
  have key : c / 3 * x ≤ c * f / Real.log r := by
    rw [le_div_iff₀ hlr]
    have h3 : c / 3 * x * Real.log r ≤ c / 3 * x * (6 * x) :=
      mul_le_mul_of_nonneg_left hlr_le (by positivity)
    have h4 : c * (2 * x ^ 2) ≤ c * f := mul_le_mul_of_nonneg_left hf_lo hc.le
    nlinarith
  rw [Real.rpow_one, pow_zero, one_mul, one_mul]
  exact Real.exp_le_exp.mpr (by linarith)

theorem exponential_tail_third (x o r : ℝ) (f : ℕ) (hx0 : 0 < x) (ho : |o| ≤ 1 / 16) (hxf : x ≤ (f : ℝ))
    (hr_hi : r ≤ 2 * x ^ 5) :
    r * (7 / 8 + o) ^ f ≤ 2 * x ^ 5 * Real.exp (-(Real.log (16 / 15) * x ^ (1 : ℝ))) := by
  have hb0 : 0 ≤ 7 / 8 + o := by
    have := (abs_le.mp ho).1
    linarith
  have hb1 : 7 / 8 + o ≤ 15 / 16 := by
    have := (abs_le.mp ho).2
    linarith
  have hl : 0 < Real.log (16 / 15) := Real.log_pos (by norm_num)
  have hpow : (7 / 8 + o) ^ f ≤ Real.exp (-(Real.log (16 / 15) * x ^ (1 : ℝ))) := by
    calc (7 / 8 + o) ^ f ≤ (15 / 16 : ℝ) ^ f := pow_le_pow_left₀ hb0 hb1 f
      _ = Real.exp (-(Real.log (16 / 15) * (f : ℝ))) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        rw [show (15 / 16 : ℝ) = (16 / 15)⁻¹ by norm_num, Real.log_inv]
        ring
      _ ≤ Real.exp (-(Real.log (16 / 15) * x ^ (1 : ℝ))) := by
        rw [Real.rpow_one]
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hxf hl.le
        linarith
  have h5 : 0 ≤ 2 * x ^ 5 := mul_nonneg (by norm_num) (pow_nonneg hx0.le 5)
  calc r * (7 / 8 + o) ^ f ≤ 2 * x ^ 5 * (7 / 8 + o) ^ f :=
        mul_le_mul_of_nonneg_right hr_hi (pow_nonneg hb0 f)
    _ ≤ 2 * x ^ 5 * Real.exp (-(Real.log (16 / 15) * x ^ (1 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow h5

theorem exponential_tail_second (x y f m : ℝ) (q d : ℕ) (hx0 : 0 < x) (hy : 0 < y) (hm0 : 0 ≤ m)
    (hf : f ≤ 2 * x ^ 3) (hm : m ≤ 2 * x ^ 3) (hq : y ≤ Real.log q) (hd : y ≤ Real.log d) :
    f * m / ((min q d : ℕ) : ℝ) ≤ 4 * x ^ 6 * Real.exp (-(1 * y)) := by
  have eq' : Real.exp y ≤ (q : ℝ) := exp_le_natCast q y hy hq
  have ed' : Real.exp y ≤ (d : ℝ) := exp_le_natCast d y hy hd
  have hmin : Real.exp y ≤ ((min q d : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min eq' ed'
  have hey : 0 < Real.exp y := Real.exp_pos y
  have hmin0 : 0 < ((min q d : ℕ) : ℝ) := lt_of_lt_of_le hey hmin
  have hx3 : 0 ≤ 2 * x ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hx0.le 3)
  have hfm : f * m ≤ 4 * x ^ 6 := by
    calc f * m ≤ 2 * x ^ 3 * m := mul_le_mul_of_nonneg_right hf hm0
      _ ≤ 2 * x ^ 3 * (2 * x ^ 3) := mul_le_mul_of_nonneg_left hm hx3
      _ = 4 * x ^ 6 := by ring
  have h6 : 0 ≤ 4 * x ^ 6 := mul_nonneg (by norm_num) (pow_nonneg hx0.le 6)
  calc f * m / ((min q d : ℕ) : ℝ) ≤ 4 * x ^ 6 / ((min q d : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hfm hmin0.le
    _ ≤ 4 * x ^ 6 / Real.exp y := div_le_div_of_nonneg_left h6 hey hmin
    _ = 4 * x ^ 6 * Real.exp (-(1 * y)) := by
        rw [one_mul, Real.exp_neg, div_eq_mul_inv]

theorem exponential_tail_first (x ε f r k : ℝ) (g : ℕ) (hx1 : 1 ≤ x) (hε0 : 0 < ε) (hε1 : ε < 1 / 52)
    (hr0 : 0 ≤ r) (hk1 : 1 ≤ k) (hf : f ≤ 2 * x ^ 3) (hr : r ≤ 2 * x ^ 5)
    (g1 : (k * Real.exp (x ^ ε)) ^ 8 ≤ (g : ℝ)) (g3 : Real.log g ≤ x ^ (ε / 100) * x ^ ε) :
    f * r ^ 5 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 64 * x ^ 29 * Real.exp (-(4 * x ^ ε)) := by
  have hx0 : 0 < x := by linarith
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le ε
  have hE : 0 < Real.exp (x ^ ε) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp (x ^ ε) := Real.one_le_exp hxe
  have hg8 : Real.exp (8 * x ^ ε) ≤ (g : ℝ) := by
    calc Real.exp (8 * x ^ ε) = Real.exp (x ^ ε) ^ 8 := by
          rw [← Real.exp_nat_mul]
          norm_num
      _ ≤ (k * Real.exp (x ^ ε)) ^ 8 := by
          apply pow_le_pow_left₀ hE.le
          nlinarith
      _ ≤ g := g1
  have hg0 : 0 < (g : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hg8
  have hlg : 8 * x ^ ε ≤ Real.log g := by
    have := Real.log_le_log (Real.exp_pos _) hg8
    rwa [Real.log_exp] at this
  have hlg0 : 0 ≤ Real.log g := le_trans (mul_nonneg (by norm_num) hxe) hlg
  have hgpow : (g : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-(4 * x ^ ε)) := by
    rw [Real.rpow_def_of_pos hg0]
    apply Real.exp_le_exp.mpr
    linarith
  have hgpow0 : 0 ≤ (g : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hg0.le _
  have hlgx : Real.log g ≤ x := by
    calc Real.log g ≤ x ^ (ε / 100) * x ^ ε := g3
      _ = x ^ (ε / 100 + ε) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hr5 : r ^ 5 ≤ (2 * x ^ 5) ^ 5 := pow_le_pow_left₀ hr0 hr 5
  have hr50 : 0 ≤ r ^ 5 := pow_nonneg hr0 5
  have hx3 : 0 ≤ 2 * x ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hx0.le 3)
  have A0 : 0 ≤ 2 * x ^ 3 * (2 * x ^ 5) ^ 5 :=
    mul_nonneg hx3 (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0.le 5)) 5)
  have A1 : f * r ^ 5 ≤ 2 * x ^ 3 * (2 * x ^ 5) ^ 5 := mul_le_mul hf hr5 hr50 hx3
  have A2 : f * r ^ 5 * Real.log g ≤ 2 * x ^ 3 * (2 * x ^ 5) ^ 5 * x := mul_le_mul A1 hlgx hlg0 A0
  have A3 : f * r ^ 5 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * x ^ 3 * (2 * x ^ 5) ^ 5 * x * Real.exp (-(4 * x ^ ε)) :=
    mul_le_mul A2 hgpow hgpow0 (mul_nonneg A0 hx0.le)
  calc f * r ^ 5 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 2 * x ^ 3 * (2 * x ^ 5) ^ 5 * x * Real.exp (-(4 * x ^ ε)) := A3
    _ = 64 * x ^ 29 * Real.exp (-(4 * x ^ ε)) := by ring

theorem sizes_basic {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hK : SizeK L) (hx1 : 1 ≤ L.sc.x) :
    2 * L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧ (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 3 ∧ (D.R.m : ℝ) ≤ 2 * L.sc.x ^ 3 ∧
      (D.R.r : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ 2 ≤ (D.R.r : ℝ) ∧ 1 ≤ (D.R.k : ℝ) := by
  have hε0 := L.sc.eps_pos
  have hε1 := L.sc.eps_lt
  unfold SizeN szTh at hN
  unfold SizeK szTh at hK
  generalize L.sc.eps = ε at *
  generalize L.sc.x = x at *
  have hfn : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by simp [Ranks.f]
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast (D.R.m_le_f : D.R.m ≤ D.R.f)
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (D.R.f_le_k : D.R.f ≤ D.R.k)
  have hrk : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have : D.R.r ≤ 2 * D.R.k := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
    exact_mod_cast this
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by have := D.R.two_le_m; unfold Ranks.r; omega
    exact_mod_cast this
  have hn_lo : x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast x 2]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hn_hi : (D.R.n : ℝ) ≤ x ^ 3 := by
    refine le_trans hN.2 ?_
    rw [← Real.rpow_natCast x 3]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hk_hi : (D.R.k : ℝ) ≤ x ^ 5 := by
    refine le_trans hK.2 ?_
    rw [← Real.rpow_natCast x 5]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hxx : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem combined_tail_le {D : D7} (L : SizeData₂ D) (hs : SizesAt L) (c o : ℝ) (hc : 0 < c) (ho : |o| ≤ 1 / 16)
    (hx2 : 2 ≤ L.sc.x) :
    0 ≤ Formalism.MainNotions.ArithmeticCylinders.br2 D c o ∧ Formalism.MainNotions.ArithmeticCylinders.br2 D c o ≤
      128 * L.sc.x ^ 29 * Real.exp (-(4 * L.sc.x ^ L.sc.eps)) +
      4 * L.sc.x ^ 6 * Real.exp (-(1 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100))) +
      2 * L.sc.x ^ 5 * Real.exp (-(Real.log (16 / 15) * L.sc.x ^ (1 : ℝ))) +
      1 * L.sc.x ^ 0 * Real.exp (-(c / 3 * L.sc.x ^ (1 : ℝ))) := by
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨hf_lo, hf_hi, hm_hi, hr_hi, hr2, hk1⟩ := sizes_basic L hs.1 hs.2.2.1 hx1
  have hQD : SizeQD L := hs.2.2.2.2.2.2.1
  have hG : SizeG L := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxf : L.sc.x ≤ (D.R.f : ℝ) := by nlinarith
  have t4 := exponential_tail_fourth L.sc.x c D.R.f D.R.r hx2 hc hf_lo hr_hi hr2
  have t3 := exponential_tail_third L.sc.x o D.R.r D.R.f hx0 ho hxf hr_hi
  have t2 := exponential_tail_second L.sc.x (L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100)) D.R.f D.R.m D.host.q D.host.d hx0
    (Real.rpow_pos_of_pos hx0 _) (Nat.cast_nonneg _) hf_hi hm_hi hQD.2.1 hQD.2.2.2.1
  have t1 : ∀ i : Fin 2, _ := fun i => exponential_tail_first L.sc.x L.sc.eps D.R.f D.R.r D.R.k (D.host.g i) hx1
    L.sc.eps_pos L.sc.eps_lt (Nat.cast_nonneg _) hk1 hf_hi hr_hi (hG i i).1 (hG i i).2.2
  have hb0 : 0 ≤ 7 / 8 + o := by have := (abs_le.1 ho).1; linarith
  constructor
  · unfold Formalism.MainNotions.ArithmeticCylinders.br2
    have h1 : 0 ≤ ∑ i : Fin 2, (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) *
        (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_nonneg
      intro i _
      have hlg0 : 0 ≤ Real.log (D.host.g i) := Real.log_natCast_nonneg _
      have hgp0 : 0 ≤ (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have h2 : 0 ≤ (D.R.f : ℝ) * D.R.m / ((min D.host.q D.host.d : ℕ) : ℝ) := by positivity
    have h3 : 0 ≤ (D.R.r : ℝ) * (7 / 8 + o) ^ D.R.f := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb0 _)
    have h4 := (Real.exp_pos (-(c * D.R.f / Real.log D.R.r))).le
    linarith
  · unfold Formalism.MainNotions.ArithmeticCylinders.br2
    rw [Fin.sum_univ_two]
    have a0 := t1 0
    have a1 := t1 1
    linarith

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i).sc.eps_pos
  rwa [Fm.L_eps] at h

theorem eps_lt {eps : ℝ} (Fm : FamP eps) : eps < 1 / 52 := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i).sc.eps_lt
  rwa [Fm.L_eps] at h

private theorem fam_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i).sc.ez_pos
  unfold Scale.ez at h
  rw [Fm.L_eps, Fm.L_J] at h
  exact h

private theorem fam_ez_le {eps : ℝ} (Fm : FamP eps) : Fm.ez ≤ eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have hJ := (Fm.L 0 i).sc.one_le_J
  rw [Fm.L_J] at hJ
  show eps / Fm.J ≤ eps
  exact div_le_self (eps_pos Fm).le hJ

theorem parX {eps : ℝ} (Fm : FamP eps) : Formalism.MainNotions.ArithmeticCylinders.ParX Fm := by
  intro C c o hc ho
  have heps := eps_pos Fm
  have heps1 := eps_lt Fm
  have hez := fam_ez_pos Fm
  have hez1 := fam_ez_le Fm
  have e1 := ev_pow (4 * |C| * 128) 29 4 eps (Fm.ez / 7) (by norm_num) heps (by linarith)
  have e2 := ev_pow (4 * |C| * 4) 6 1 (Fm.ez / 5 - Fm.ez / 100) (Fm.ez / 7) one_pos (by linarith) (by linarith)
  have e3 := ev_pow (4 * |C| * 2) 5 (Real.log (16 / 15)) 1 (Fm.ez / 7) (Real.log_pos (by norm_num)) one_pos
    (by linarith)
  have e4 := ev_pow (4 * |C| * 1) 0 (c / 3) 1 (Fm.ez / 7) (by positivity) one_pos (by linarith)
  have eo : ∀ᶠ x in atTop, |o x| ≤ 1 / 16 := by
    have := ho.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 16))
    filter_upwards [this] with x hx
    simpa [Real.dist_eq] using hx
  obtain ⟨x0, h0⟩ := (e1.and (e2.and (e3.and (e4.and (eo.and
    ((eventually_gt_atTop Fm.x1).and (eventually_ge_atTop 2))))))).exists_forall_of_atTop
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨a1, a2, a3, a4, ao, hx1, hx2⟩ := h0 x hx
  have hX := Fm.L_x x i hx1
  have hE := Fm.L_eps x i
  have hbr := combined_tail_le (Fm.L x i) (Fm.sizes x hx1 i) c (o x) hc ao (by rw [hX]; exact hx2)
  rw [hX, hE, Fm.L_ez x i] at hbr
  obtain ⟨hnn, hle⟩ := hbr
  calc C * Formalism.MainNotions.ArithmeticCylinders.br2 (Fm.D x i) c (o x) ≤ |C| * Formalism.MainNotions.ArithmeticCylinders.br2 (Fm.D x i) c (o x) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hnn
    _ ≤ |C| * _ := mul_le_mul_of_nonneg_left hle (abs_nonneg C)
    _ ≤ Real.exp (-(x ^ (Fm.ez / 7))) := by linarith

theorem parO {eps : ℝ} (Fm : FamP eps) : Formalism.MainNotions.ArithmeticCylinders.ParO Fm := by
  intro δ hδ
  have heps := eps_pos Fm
  have e1 := ev_pow (4 / δ) 10 8 eps (eps / 2) (by norm_num) heps (by linarith)
  obtain ⟨x0, h0⟩ := (e1.and ((eventually_gt_atTop Fm.x1).and (eventually_ge_atTop 1))).exists_forall_of_atTop
  refine ⟨x0, fun x hx i k => ?_⟩
  obtain ⟨a1, hx1, hx2⟩ := h0 x hx
  have hX := Fm.L_x x i hx1
  have hE := Fm.L_eps x i
  have hs := Fm.sizes x hx1 i
  obtain ⟨-, -, -, hr_hi, hr2, hk1⟩ := sizes_basic (Fm.L x i) hs.1 hs.2.2.1 (by rw [hX]; exact hx2)
  have hG : SizeG (Fm.L x i) := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have g1 : (((Fm.D x i).R.k : ℝ) * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)) ^ 8 ≤
      ((Fm.D x i).host.g k : ℝ) := (hG k k).1
  rw [hX] at hr_hi
  rw [hX, hE] at g1
  have hb8 : Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g k : ℝ) := by
    refine le_trans ?_ g1
    have : Real.exp (8 * x ^ eps) = Real.exp (x ^ eps) ^ 8 := by
      rw [← Real.exp_nat_mul]; congr 1
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (le_mul_of_one_le_left (Real.exp_pos _).le hk1) 8
  have hone : Real.exp (-(x ^ (eps / 2))) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (by linarith) _))
  have h2 : 4 * x ^ 10 ≤ δ * Real.exp (8 * x ^ eps) := by
    have h3 := a1.trans hone
    have hpos := Real.exp_pos (8 * x ^ eps)
    have h4 : 4 / δ * x ^ 10 * Real.exp (-(8 * x ^ eps)) = (4 * x ^ 10) / (δ * Real.exp (8 * x ^ eps)) := by
      rw [Real.exp_neg]; field_simp
    rw [h4, div_le_one (by positivity)] at h3
    exact h3
  calc ((Fm.D x i).R.r : ℝ) ^ 2 ≤ (2 * x ^ 5) ^ 2 := pow_le_pow_left₀ (by linarith) hr_hi 2
    _ = 4 * x ^ 10 := by ring
    _ ≤ δ * Real.exp (8 * x ^ eps) := h2
    _ ≤ δ * ((Fm.D x i).host.g k : ℝ) := mul_le_mul_of_nonneg_left hb8 hδ.le

theorem drows_le_dall (D : D7) : D.what₂.Drows ≤ D.what₂.Dall := by
  rw [← D.s_HH]
  have hli : LinearIndependent ℂ (fun a => D.sEE (D.what₂.onb a)) :=
    D.what₂.onb.orthonormal.linearIndependent.map_of_surjective_injective (starRingEnd ℂ)
      D.sEE.toLinearMap.toAddMonoidHom (starRingEnd ℂ).surjective
      (fun m hm => D.sEE.injective (by simpa using hm)) (fun r m => by simp)
  simpa using hli.fintype_card_le_finrank

theorem delpNonneg_of_pos (D : D7) (h : 0 < D.what₂.Dall) : Rows.DelpNonneg D.what₂ := by
  have h1 := D.what₂.D_eq
  have h2 : (D.what₂.Drows : ℝ) ≤ D.what₂.Dall := by exact_mod_cast drows_le_dall D
  have h3 : (0 : ℝ) < D.what₂.Dall := by exact_mod_cast h
  unfold Rows.DelpNonneg
  by_contra hneg
  push Not at hneg
  nlinarith

theorem all_rows_count_pos (D : D7) (A : Formalism.MainNotions.ArithmeticCylinders.AllRows D) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) (hc : 0 < c₃)
    (h : Formalism.MainNotions.ArithmeticCylinders.Adm2 D A n₀ Alev C₃ c₃ cb CL) : 0 < D.what₂.Dall := by
  obtain ⟨h1, -, hT1, -, -, ⟨b, hh, hSet, hGap, hs1, hs2, hs3, hpos⟩, -⟩ := h
  have hcyl : Formalism.MainNotions.ArithmeticCylinders.cyl D 0 (Set.univ) = Set.univ := by
    ext t; simp [Formalism.MainNotions.ArithmeticCylinders.cyl]
  obtain ⟨hS, hC⟩ := hSet 0 Set.univ
  rw [hcyl, A.eT_univ] at hS
  rw [hcyl, A.eT_univ, A.ReT_univ] at hC
  have hcount := h1 A.B.I b A.B.lam A.B.g (D.host.g (1 - 0)) A.B.e A.B.H A.B.σ A.B.w A.B.Hs A.B.σs A.B.tens
    A.B.μf A.B.fund A.B.R A.B.Re hh hS hC hGap hs1 hs2 hs3
  have hn : (2 : ℝ) ≤ A.B.I.n := by
    rw [A.n_eq]
    have : 2 ≤ D.R.r := by
      have := D.R.m_add_three_le_k
      have := D.R.two_le_m
      unfold Ranks.r; omega
    exact_mod_cast this
  have hf : (0 : ℝ) < A.B.I.f := by
    rw [A.f_eq]
    have : 0 < D.R.f := by have h : 0 < D.R.n := D.R.ord_pos; unfold Ranks.f; omega
    exact_mod_cast this
  have hlog : 0 < Real.log A.B.I.n := Real.log_pos (by linarith)
  have hlt : Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) < 1 := by
    have : 0 < c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) := by positivity
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  rw [hT1]
  unfold Formalism.MainNotions.S.RowsAut.D
  by_contra h0
  have h00 : A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R A.B.Re = 0 := by omega
  rw [h00, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hpos] at hcount
  nlinarith

def DelpNonnegF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Rows.DelpNonneg (Fm.D x i).what₂

def DallPosF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 < (Fm.D x i).what₂.Dall

theorem delpNonnegF_of {eps : ℝ} (Fm : FamP eps) (h : DallPosF Fm) : DelpNonnegF Fm := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x hx0 i => delpNonneg_of_pos _ (hx x hx0 i)⟩

theorem linkIRR_iff {eps : ℝ} (Fm : FamP eps) : LinkIRR Fm ↔ DelpNonnegF Fm ∧ Formalism.MainNotions.ArithmeticCylinders.FamilyExpDeficitBound' Fm := by
  constructor
  · rintro ⟨x0, hx⟩
    exact ⟨⟨x0, fun x hx0 i => (hx x hx0 i).1⟩, ⟨x0, fun x hx0 i => (hx x hx0 i).2⟩⟩
  · rintro ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩
    exact ⟨max x1 x2, fun x hx i =>
      ⟨h1 x (le_of_max_le_left hx) i, h2 x (le_of_max_le_right hx) i⟩⟩

theorem second_bound_of_first_family {eps : ℝ} (Fm : FamP eps) (h2 : Formalism.MainNotions.ArithmeticCylinders.Conclusion2Family Fm) : Formalism.MainNotions.ArithmeticCylinders.FamilyExpDeficitBound' Fm := by
  obtain ⟨C, c, hc, o, ho, x0, h⟩ := h2
  obtain ⟨x1, h1⟩ := parX Fm C c o hc ho
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  exact (h x (le_trans (le_max_left _ _) hx) i).trans (h1 x (le_trans (le_max_right _ _) hx) i)

theorem irreducibility_link_of_bound {eps : ℝ} (Fm : FamP eps) (h2 : Formalism.MainNotions.ArithmeticCylinders.Conclusion2Family Fm) (hD : DallPosF Fm) :
    LinkIRR Fm := (linkIRR_iff Fm).mpr ⟨delpNonnegF_of Fm hD, second_bound_of_first_family Fm h2⟩

theorem linkIRR_of {eps : ℝ} (Fm : FamP eps) (A : ∀ x (i : Fm.Ix x), Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i))
    (hS : Formalism.MainNotions.ArithmeticCylinders.KudlaFamilyStatement Fm A) (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ) (hc : 0 < c₃)
    (hA : ∀ x ≥ x₂, ∀ i : Fm.Ix x, Formalism.MainNotions.ArithmeticCylinders.Adm2 (Fm.D x i) (A x i) n₀ Alev C₃ c₃ cb CL) :
    LinkIRR Fm := by
  have hP := hS.2 n₀ Alev C₃ c₃ cb CL x₂ hc hA (parO Fm)
  have hD : DallPosF Fm :=
    ⟨x₂, fun x hx i => all_rows_count_pos _ (A x i) n₀ Alev C₃ c₃ cb CL hc (hA x hx i)⟩
  exact (linkIRR_iff Fm).mpr ⟨delpNonnegF_of Fm hD, hP.2 (parX Fm)⟩

def IrrHyp {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ (A : ∀ x (i : Fm.Ix x), Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i)) (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ),
    Formalism.MainNotions.ArithmeticCylinders.KudlaFamilyStatement Fm A ∧ 0 < c₃ ∧
      ∀ x ≥ x₂, ∀ i : Fm.Ix x, Formalism.MainNotions.ArithmeticCylinders.Adm2 (Fm.D x i) (A x i) n₀ Alev C₃ c₃ cb CL

theorem linkIRR_of_hyp {eps : ℝ} (Fm : FamP eps) (h : IrrHyp Fm) : LinkIRR Fm := by
  obtain ⟨A, n₀, Alev, C₃, c₃, cb, CL, x₂, hS, hc, hA⟩ := h
  exact linkIRR_of Fm A hS n₀ Alev C₃ c₃ cb CL x₂ hc hA

def LocsCoverF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i)

theorem linkEta_iff {eps : ℝ} (Fm : FamP eps) : LinkEta Fm ↔ LocsCoverF Fm := Iff.rfl

theorem linkEta_of {eps : ℝ} (Fm : FamP eps) (h : LocsCoverF Fm) : LinkEta Fm := (linkEta_iff Fm).mpr h

def ThetaScalarNonzero (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ D.what₂.isot j σ,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = lam • f

theorem thetaT_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) (hI : DirectSum.IsInternal (D.what₂.isot j))
    (h : ThetaScalarNonzero D μ j) : Function.Injective (D.what₂.thetaT μ j) := by
  classical
  choose lam hlam0 hlam using h
  set T : Module.End ℂ (D.what₂.Mj j) := (D.what₂.thetaP μ j).comp (D.what₂.thetaT μ j) with hTdef
  have hsub : ∀ σ, D.what₂.isot j σ ≤ Module.End.eigenspace T (lam σ) := by
    intro σ f hf
    rw [Module.End.mem_eigenspace_iff]
    exact hlam σ f hf
  have htop : (⊤ : Submodule ℂ (D.what₂.Mj j)) ≤ ⨆ (c : ℂ) (_ : c ≠ 0), Module.End.eigenspace T c := by
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun σ => le_trans (hsub σ) ?_
    exact le_iSup₂_of_le (lam σ) (hlam0 σ) le_rfl
  have hind : iSupIndep (Module.End.eigenspace T) := by
    first
      | exact Module.End.eigenspaces_iSupIndep T
      | exact Module.End.eigenspaces_independent T
  have hdis : Disjoint (Module.End.eigenspace T 0) ⊤ := (hind 0).mono_right htop
  have hker : LinearMap.ker T = ⊥ := by
    rw [← Module.End.eigenspace_zero]
    exact disjoint_top.mp hdis
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  exact Function.Injective.of_comp (f := D.what₂.thetaP μ j) hTinj

theorem finrank_Mj (D : D7) (X : DivX D) (hR : DV.MjRank D X) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  have hj' := Finset.mem_Icc.1 hj
  have hb := X.jM_basis j
  have h1 : Module.finrank ℂ (D.what₂.Mj j) = Fintype.card (X.MjH j).ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hb.1 hb.2.ge)
  have h2 : (X.MjH j).rank = Fintype.card (X.MjH j).ι := by
    unfold HLat.rank Formalism.HN.rkK
    rw [(X.MjH_good j).2.2, finrank_top]
    exact Module.finrank_eq_card_basis (X.MjH j).b
  rw [h1, ← h2, hR j hj'.1 hj'.2]

theorem finrank_Zj (D : D7) (X : DivX D) (hR : DV.MjRank D X) (μ : D.what₂.Tup) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (hI : DirectSum.IsInternal (D.what₂.isot j)) (h : ThetaScalarNonzero D μ j) :
    Module.finrank ℂ (D.what₂.Zj μ j) = D.what₂.D0 := by
  have hinj := thetaT_injective D μ j hI h
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hinj]
  exact finrank_Mj D X hR j hj

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

theorem theta_scalar_of_positivity (D : D7) (μ : D.what₂.Tup) (j : ℕ) (h : LamPos D μ j) : ThetaScalarNonzero D μ j := by
  intro σ
  obtain ⟨h1, h2⟩ := h σ
  by_cases hb : D.what₂.isot j σ = ⊥
  · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    simp
  · exact ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (h2 hb).ne', h1⟩

theorem theta_scalar_of_eigenvalue (D : D7) (h : Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching D) (μ : D.what₂.Tup) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    ThetaScalarNonzero D μ j := by
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := by
    unfold SizeData₂.lifts at hj
    simpa using hj
  have hin : CanonicalTranslateJets.InR D j := by
    first
      | exact hj
      | exact hj'
      | (unfold CanonicalTranslateJets.InR; first | exact hj | exact hj' | simpa using hj' | omega)
  exact theta_scalar_of_positivity D μ j (h μ j hin)

theorem theta_scalar_of_proposition (D : D7) (h : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (i : D.nd.Loc) :
    ThetaScalarNonzero D (D.nd.mu i) (D.nd.j i) := by
  have h1 := h i
  unfold SumRepresentations.At.Conclusion42 at h1
  intro σ
  by_cases hb : D.what₂.isot (D.nd.j i) σ = ⊥
  · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    simp
  · obtain ⟨lam, hlam, hf⟩ := ((h1 σ hb).1).1
    exact ⟨(lam : ℂ), Complex.ofReal_ne_zero.mpr hlam.ne', hf⟩

theorem rank_invariant_at_localisation {D : D7} (L : SizeData₂ D) (X : DivX D) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (hI : Rows.IsotInternal D.what₂) (hR : DV.MjRank D X) (i : D.nd.Loc) :
    L.zeroSpaceRankAtPlace (D.nd.j i) (D.nd.w i) = D.what₂.D0 := by
  have h42i := theta_scalar_of_proposition D h42 i
  have hjr := D.nd.j_range i
  have hj : D.nd.j i ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    simpa using hjr
  have hmu : D.nd.mu i = D.what₂.muTw (D.nd.w i) := by
    first
      | exact D.nd.mu_eq i
      | exact D.nd.mu_tw i
      | exact D.nd.mu_w i
      | exact D.nd.mu_def i
      | exact D.nd.muTw_eq i
      | exact D.nd.hmu i
      | exact D.nd.mu_spec i
      | exact (D.nd.mu_eq i).symm
      | rfl
  rw [hmu] at h42i
  unfold SizeData₂.zeroSpaceRankAtPlace
  exact finrank_Zj D X hR _ _ hj (hI _ hjr.1 hjr.2) h42i

def LocNe (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, ∃ i : D.nd.Loc, D.nd.j i = j

theorem rank_invariant_of_constancy {D : D7} (L : SizeData₂ D) (X : DivX D) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (hI : Rows.IsotInternal D.what₂) (hR : DV.MjRank D X) (hne : LocNe D) (h3 : Formalism.MainNotions.TwistedPlaces.adm3 L) :
    ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0 := by
  intro j hj
  obtain ⟨i, rfl⟩ := hne j hj
  unfold TwistedPlaces.adm3 at h3
  have htw : D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 := by
    first
      | exact D.nd.w_tw i
      | exact D.nd.tw i
      | exact D.nd.mu_ne i
      | exact D.nd.twisted i
      | exact D.nd.w_twisted i
      | exact D.nd.muAt_ne i
  rw [← h3 _ hj _ htw]
  exact rank_invariant_at_localisation L X h42 hI hR i

theorem rank_equal_at_every_place {D : D7} (L : SizeData₂ D) (X : DivX D) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (hI : Rows.IsotInternal D.what₂) (hR : DV.MjRank D X)
    (hZ : ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0) (i : D.nd.Loc) :
    L.zeroSpaceRankAtPlace (D.nd.j i) (D.nd.w i) = L.dZ0 (D.nd.j i) := by
  have hjr := D.nd.j_range i
  have hj : D.nd.j i ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    simpa using hjr
  rw [rank_invariant_at_localisation L X h42 hI hR i, hZ _ hj]

theorem rank_invariant_of_nonzero_scalar {D : D7} (L : SizeData₂ D) (X : DivX D) (hI : Rows.IsotInternal D.what₂)
    (hR : DV.MjRank D X) (h0 : ∀ j ∈ SizeData₂.lifts D, ThetaScalarNonzero D D.what₂.mu0 j) :
    ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0 := by
  intro j hj
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := by
    unfold SizeData₂.lifts at hj
    simpa using hj
  unfold SizeData₂.dZ0
  exact finrank_Zj D X hR D.what₂.mu0 j hj (hI j hj'.1 hj'.2) (h0 j hj)

def IsotF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Rows.IsotInternal (Fm.D x i).what₂

def MjRankF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, DV.MjRank (Fm.D x i) (Fm.X x i)

def LocNeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LocNe (Fm.D x i)

def ThetaScalarReferenceFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ThetaScalarNonzero (Fm.D x i) (Fm.D x i).what₂.mu0 j

def EigenvalueAdmittedFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching (Fm.D x i)

theorem eigenvalue_family_of_admitted {eps : ℝ} (Fm : FamP eps) (GF : Formalism.MainNotions.CanonicalTranslateJets.LocF Fm) (h : Formalism.MainNotions.CanonicalTranslateJets.AdmF Fm GF) :
    EigenvalueAdmittedFamily Fm := by
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hA := h x (by linarith) i
  unfold CanonicalTranslateJets.admitted at hA
  exact hA.2.2.2.1

theorem theta_scalar_family_of_eigenvalue {eps : ℝ} (Fm : FamP eps) (h : EigenvalueAdmittedFamily Fm) : ThetaScalarReferenceFamily Fm := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x hx0 i j hj => theta_scalar_of_eigenvalue _ (hx x hx0 i) _ j hj⟩

theorem rank_invariant_family_of_scalar {eps : ℝ} (Fm : FamP eps) (h0 : ThetaScalarReferenceFamily Fm) (hI : IsotF Fm) (hR : MjRankF Fm) :
    SmallLevelRankEq Fm := by
  obtain ⟨x1, h1⟩ := h0
  obtain ⟨x2, h2⟩ := hI
  obtain ⟨x3, h3⟩ := hR
  refine ⟨max x1 (max x2 x3), fun x hx i => ?_⟩
  have hx23 := le_of_max_le_right hx
  exact rank_invariant_of_nonzero_scalar (Fm.L x i) (Fm.X x i) (h2 x (le_of_max_le_left hx23) i)
    (h3 x (le_of_max_le_right hx23) i) (h1 x (le_of_max_le_left hx) i)

theorem rank_invariant_of_eigenvalue {eps : ℝ} (Fm : FamP eps) (h : EigenvalueAdmittedFamily Fm) (hI : IsotF Fm) (hR : MjRankF Fm) :
    SmallLevelRankEq Fm := rank_invariant_family_of_scalar Fm (theta_scalar_family_of_eigenvalue Fm h) hI hR

def Adm3F {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.TwistedPlaces.adm3 (Fm.L x i)

theorem rank_input_of_finiteness {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hF : LinkShaFin Fm) : Adm3F Fm := by
  obtain ⟨C, x0, hx⟩ := hA
  obtain ⟨x1, hF1⟩ := hF
  refine ⟨max (max x0 x1) (Fm.x1 + 1), fun x hx' i => ?_⟩
  have hxa := le_of_max_le_left hx'
  obtain ⟨tb, htb⟩ := hx x (le_of_max_le_left hxa) (by have := le_of_max_le_right hx'; linarith) i
    (hF1 x (le_of_max_le_right hxa) i)
  unfold TwistedPlaces.AdmT at htb
  exact htb.2.2.1

theorem rank_invariant_family_of {eps : ℝ} (Fm : FamP eps) (h32 : Formalism.MainNotions.SumRepresentations.ConclusionF1 Fm) (hI : IsotF Fm) (hR : MjRankF Fm)
    (hne : LocNeF Fm) (h3 : Adm3F Fm) : SmallLevelRankEq Fm := by
  obtain ⟨x1, h1⟩ := h32
  obtain ⟨x2, h2⟩ := hI
  obtain ⟨x3, h3'⟩ := hR
  obtain ⟨x4, h4⟩ := hne
  obtain ⟨x5, h5⟩ := h3
  refine ⟨max (max x1 x2) (max x3 (max x4 x5)), fun x hx i => ?_⟩
  have ha := le_of_max_le_left hx
  have hb := le_of_max_le_right hx
  have hc := le_of_max_le_right hb
  have hp := h1 x (le_of_max_le_left ha) i
  have h42 : SumRepresentations.Conclusion42 (Fm.D x i) := by
    first
      | exact hp.1
      | exact hp.2
      | exact hp.2.1
      | exact hp.2.2
      | exact hp.2.2.1
      | exact hp.1.2
      | (unfold SumRepresentations.Conclusion1 at hp; first | exact hp.1 | exact hp.2 | exact hp.2.1 | exact hp.2.2 | exact hp.2.2.1 | exact hp.2.2.2)
      | (unfold SumRepresentations.Conclusion1 at hp; exact hp)
  exact rank_invariant_of_constancy (Fm.L x i) (Fm.X x i) h42 (h2 x (le_of_max_le_right ha) i)
    (h3' x (le_of_max_le_left hb) i) (h4 x (le_of_max_le_left hc) i) (h5 x (le_of_max_le_right hc) i)

end Formalism.MainNotions.N

end

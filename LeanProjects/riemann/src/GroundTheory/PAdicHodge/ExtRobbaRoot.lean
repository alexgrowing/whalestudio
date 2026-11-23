import Mathlib
import GroundTheory.PAdicHodge.ExistsIsRootForallNormPowMulLe
import GroundTheory.PAdicHodge.ExtRobbaPointDiv
import GroundTheory.PAdicHodge.ExtRobbaUnits
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem teich_mul_int_mem_Econ (z : L) {V : Γ} (hV : V ∈ T.int) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B (T.teich z * V) ∈ T.Econ ρ0 := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_zcoeff_mul ρ0.2.1 ρ0.2.2 (T.convergesAt_teich z _)
    (T.convergesAt_of_mem_int hV ρ0.2.1 ρ0.2.2)

def liftExt (ρ0 : Set.Ioo (0 : ℝ) 1) (z : L) {V : Γ} (hV : V ∈ T.int) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.teich z * V), T.teich_mul_int_mem_Econ z hV ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0)

theorem extNorm_liftExt {ρ0 : Set.Ioo (0 : ℝ) 1} (z : L) {V : Γ} (hV : V ∈ T.int)
    (h1 : ‖T.red V‖ = 1) (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (T.liftExt ρ0 z hV) = ‖z‖ := by
  rw [liftExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B (T.teich z * V))) σ = ‖z‖
  rw [coeffB_algebraMap, T.gaussNorm_zcoeff_mul (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)
    (T.convergesAt_teich z _) (T.convergesAt_of_mem_int hV (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)),
    T.gaussNorm_teich z (rad_pos ρ0 σ),
    T.gaussNorm_eq_one_of_mem_int hV h1 (rad_pos ρ0 σ) (rad_lt_one ρ0 σ), mul_one]

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)

theorem convergesAt_one_ptRad : ConvergesAt (T.zcoeff (1 : Γ)) (T.ptRad ξ) := by
  rw [zcoeff_one]; exact convergesAt_pi_single _ _ _

theorem ptE_teich (a : L) : T.ptE hξ (T.teich a) = T.ptSharp hξ a := by
  have := T.ptE_teich_mul hξ a 1 (T.convergesAt_one_ptRad (ξ := ξ))
  rwa [mul_one, ptE_one, mul_one] at this

theorem ptE_π : T.ptE hξ T.π = T.ptPi hξ := by
  have := T.ptE_π_pow hξ 1
  rwa [pow_one, pow_one] at this

theorem ptEval_liftExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ ≤ ρ0) (z : L) {V : Γ}
    (hV : V ∈ T.int) :
    T.ptEval hξ hr (T.liftExt ρ0 z hV) = T.ptSharp hξ z * T.ptE hξ V := by
  rw [liftExt, ptEval_coe]
  show T.ptEvalB hξ (algebraMap Γ T.B (T.teich z * V)) = _
  rw [ptEvalB_algebraMap, T.ptE_teich_mul hξ z V
    (T.convergesAt_of_mem_int hV (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ))]

theorem norm_ptE_int_le {Y : Γ} (hY : Y ∈ T.int) :
    ‖T.ptE hξ Y‖ ≤ max ‖T.red Y‖ (T.ptRad ξ) := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have ht := T.tail_mem_int hY
  have htc := T.convergesAt_of_mem_int ht hr0 hr1
  have hc1 : ConvergesAt (T.zcoeff (T.teich (T.red Y))) (T.ptRad ξ) := T.convergesAt_teich _ _
  have hc2 : ConvergesAt (T.zcoeff (T.π * T.tail Y)) (T.ptRad ξ) :=
    T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc
  have hYe := T.eq_teich_add_π_mul_tail Y
  have e : T.ptE hξ Y = T.ptSharp hξ (T.red Y) + T.ptPi hξ * T.ptE hξ (T.tail Y) := by
    conv_lhs => rw [hYe]
    rw [T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · rw [norm_ptSharp]
  · rw [norm_mul, norm_ptPi]
    have h1 : ‖T.ptE hξ (T.tail Y)‖ ≤ 1 :=
      (T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)
    calc ‖T.coeff (ξ : Γ) 0‖ * ‖T.ptE hξ (T.tail Y)‖ ≤ ‖T.coeff (ξ : Γ) 0‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = T.ptRad ξ := mul_one _

theorem exists_lift_value' (w : T.UntiltField hξ) :
    ∃ (z : L) (V : Γ) (hV : V ∈ T.int), ‖T.red V‖ = 1 ∧ ‖z‖ = ‖w‖ ∧
      T.ptSharp hξ z * T.ptE hξ V = w := by
  by_cases hw0 : w = 0
  · refine ⟨0, 1, T.int.one_mem, by rw [map_one, norm_one], by rw [hw0, norm_zero, norm_zero], ?_⟩
    rw [map_zero, zero_mul, hw0]
  obtain ⟨d, hd⟩ := NormedField.exists_lt_norm L ‖w‖
  have hd0 : d ≠ 0 := by rintro rfl; rw [norm_zero] at hd; exact absurd hd (not_lt.2 (norm_nonneg _))
  have hsd : T.ptSharp hξ d ≠ 0 := T.sharp_ne_zero hξ hd0
  set w' := w / T.ptSharp hξ d with hw'
  have hw'1 : ‖w'‖ ≤ 1 := by
    rw [hw', norm_div, norm_ptSharp, div_le_one (norm_pos_iff.2 hd0)]; exact hd.le
  obtain ⟨z', hz', V, hV, hVe⟩ := T.exists_lift_value hξ hw'1
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hVc := T.convergesAt_of_mem_int hV hr0 hr1
  rw [T.ptE_teich_mul hξ z' V hVc] at hVe
  have hw'0 : w' ≠ 0 := div_ne_zero hw0 hsd
  have hz'0 : z' ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at hVe; exact hw'0 hVe.symm
  have hnV : ‖T.ptE hξ V‖ = 1 := by
    have := congrArg norm hVe
    rw [norm_mul, norm_ptSharp, hz'] at this
    have hpos : 0 < ‖w'‖ := norm_pos_iff.2 hw'0
    field_simp at this
    nlinarith [this]
  have hred : ‖T.red V‖ = 1 := by
    refine le_antisymm (T.norm_red_le_one V hV) ?_
    have := T.norm_ptE_int_le hξ hV
    rw [hnV] at this
    rcases le_max_iff.1 this with h | h
    · exact h
    · exact absurd h (not_le.2 hr1)
  refine ⟨d * z', V, hV, hred, ?_, ?_⟩
  · rw [norm_mul, hz', hw', norm_div, norm_ptSharp]
    field_simp
  · rw [map_mul, mul_assoc, hVe, hw', mul_div_cancel₀ _ hsd]

theorem prefixLe_teich' (c : L) (n : ℕ) {b : ℝ} (hb : ‖c‖ ≤ b) : T.PrefixLe (T.teich c) n b := by
  have := T.prefixLe_π_pow_mul_teich 0 c n ((norm_nonneg c).trans hb) fun _ => hb
  rwa [pow_zero, one_mul] at this

theorem norm_sharp_add_sub_le (a b : L) :
    ‖T.ptSharp hξ a + T.ptSharp hξ b - T.ptSharp hξ (a + b)‖ ≤ T.ptRad ξ * max ‖a‖ ‖b‖ := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  set M := max ‖a‖ ‖b‖
  have hM0 : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  set D := T.teich a + T.teich b - T.teich (a + b) with hD
  have hDred : T.red D = 0 := by simp [D, red_teich]
  have hDe : D = T.π * T.tail D := by
    have := T.sub_teich_eq_π_mul_tail D
    rwa [hDred, T.teich_zero, sub_zero] at this
  have hpre : ∀ n, T.PrefixLe D n M := fun n =>
    T.prefixLe_sub (T.prefixLe_add (T.prefixLe_teich' a n (le_max_left _ _))
      (T.prefixLe_teich' b n (le_max_right _ _)))
      (T.prefixLe_teich' (a + b) n ((IsUltrametricDist.norm_add_le_max _ _).trans le_rfl))
  have htail : ∀ n, ‖T.coeff (T.tail D) n‖ ≤ M := fun n => by
    rw [← coeff_succ]; exact hpre (n + 1) (n + 1) le_rfl
  have hbdd : T.IsBddElt (T.tail D) := T.isBddElt_of_le htail
  have htc : ConvergesAt (T.zcoeff (T.tail D)) (T.ptRad ξ) := T.convergesAt_of_isBddElt hbdd hr0 hr1
  have hgn : gaussNorm (T.zcoeff (T.tail D)) (T.ptRad ξ) ≤ M := by
    refine gaussNorm_le fun n => ?_
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact hM0
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [T.zcoeff_natCast, zpow_natCast]
    calc ‖T.coeff (T.tail D) k‖ * T.ptRad ξ ^ k ≤ M * 1 :=
          mul_le_mul (htail k) (pow_le_one₀ hr0.le hr1.le) (by positivity) hM0
      _ = M := mul_one M
  have hc : ∀ c : L, ConvergesAt (T.zcoeff (T.teich c)) (T.ptRad ξ) := fun c => T.convergesAt_teich c _
  have hval : T.ptE hξ D = T.ptSharp hξ a + T.ptSharp hξ b - T.ptSharp hξ (a + b) := by
    rw [hD, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_zcoeff_add hr0 hr1 (hc a) (hc b))
      (T.convergesAt_zcoeff_neg hr0 hr1 (hc _)), T.ptE_add hξ (hc a) (hc b),
      T.ptE_neg hξ (hc _), ptE_teich, ptE_teich, ptE_teich, ← sub_eq_add_neg]
  rw [← hval, hDe, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_π, norm_mul, norm_ptPi]
  exact mul_le_mul_of_nonneg_left ((T.norm_ptE_le hξ htc).trans hgn) (norm_nonneg _)

theorem norm_sum_sharp_sub_le {ι : Type*} (s : Finset ι) (a : ι → L) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ‖∑ i ∈ s, T.ptSharp hξ (a i) - T.ptSharp hξ (∑ i ∈ s, a i)‖ ≤ T.ptRad ξ * M := by
  classical
  have hr0 := T.ptRad_pos' hξ
  suffices H : ‖∑ i ∈ s, a i‖ ≤ M ∧
      ‖∑ i ∈ s, T.ptSharp hξ (a i) - T.ptSharp hξ (∑ i ∈ s, a i)‖ ≤ T.ptRad ξ * M from H.2
  induction s using Finset.induction_on with
  | empty => simp [hM0, mul_nonneg hr0.le hM0]
  | insert i s hi ih =>
    have ih' := ih fun j hj => hM j (Finset.mem_insert_of_mem hj)
    have hai := hM i (Finset.mem_insert_self i s)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hai ih'.1), ?_⟩
    have e : T.ptSharp hξ (a i) + ∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j) =
        (∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (∑ j ∈ s, a j)) +
        (T.ptSharp hξ (a i) + T.ptSharp hξ (∑ j ∈ s, a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j)) := by
      ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih'.2 ?_)
    exact (T.norm_sharp_add_sub_le hξ _ _).trans
      (mul_le_mul_of_nonneg_left (max_le hai ih'.1) hr0.le)

include hξ in
theorem ξExt_ne_zero {ρ0 : Set.Ioo (0 : ℝ) 1} : T.ξExt ξ ρ0 ≠ 0 := by
  intro h
  have := T.ptRad_le_extNorm_ξExt (ξ := ξ) (topRad ρ0)
  rw [h, extNorm_zero] at this
  exact absurd this (not_le.2 (T.ptRad_pos' hξ))

include hξ in

theorem idx_ξExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0) :
    T.lowIdx (T.ξExt ξ ρ0) (T.ptRad ξ) = 0 ∧ T.highIdx (T.ξExt ξ ρ0) (T.ptRad ξ) = 1 := by
  obtain ⟨h1, h2⟩ := T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩)
    (T.ξExt_ne_zero hξ) ⟨T.ptRad_pos' hξ, hr⟩
  have e : T.coeffB ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) : T.B) =
      T.zcoeff (ξ : Γ) := T.coeffB_algebraMap _
  rw [e] at h1 h2
  obtain ⟨h3, h4⟩ := T.idx_prim_self hξ
  exact ⟨h1.trans h3, h2.trans h4⟩

include hξ in

theorem mult_ξExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0) :
    T.mult (T.ξExt ξ ρ0) (T.ptRad ξ) = 1 := by
  rw [mult, (T.idx_ξExt hξ hr).1, (T.idx_ξExt hξ hr).2]; rfl

section Taylor

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

include hξ in
theorem extNorm_ξExt (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (T.ξExt ξ ρ0) = max (T.ptRad ξ) σ := by
  rw [ξExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) σ = _
  rw [coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)]
  rfl

variable (hr : T.ptRad ξ ≤ ρ0)

structure DivStep (y : T.RobbaExt ρ0) where

  z : L

  V : Γ
  hV : V ∈ T.int
  hred : ‖T.red V‖ = 1
  hz : ‖z‖ = ‖T.ptEval hξ hr y‖
  hval : T.ptSharp hξ z * T.ptE hξ V = T.ptEval hξ hr y

  next : T.RobbaExt ρ0
  eq : y = T.liftExt ρ0 z hV + T.ξExt ξ ρ0 * next

theorem nonempty_divStep (y : T.RobbaExt ρ0) : Nonempty (T.DivStep hξ hr y) := by
  obtain ⟨z, V, hV, hred, hz, hval⟩ := T.exists_lift_value' hξ (T.ptEval hξ hr y)
  have h0 : T.ptEval hξ hr (y - T.liftExt ρ0 z hV) = 0 := by
    rw [map_sub, T.ptEval_liftExt hξ hr z hV, hval, sub_self]
  obtain ⟨y', hy'⟩ := (T.ptEval_eq_zero_iff hξ hr _).1 h0
  exact ⟨⟨z, V, hV, hred, hz, hval, y', by rw [← hy']; ring⟩⟩

def divStep (y : T.RobbaExt ρ0) : T.DivStep hξ hr y := Classical.choice (T.nonempty_divStep hξ hr y)

def tay (x : T.RobbaExt ρ0) : ℕ → T.RobbaExt ρ0
  | 0 => x
  | j + 1 => (T.divStep hξ hr (tay x j)).next

theorem tay_zero (x : T.RobbaExt ρ0) : T.tay hξ hr x 0 = x := rfl

theorem tay_succ (x : T.RobbaExt ρ0) (j : ℕ) :
    T.tay hξ hr x (j + 1) = (T.divStep hξ hr (T.tay hξ hr x j)).next := rfl

theorem taylor_eq (x : T.RobbaExt ρ0) (J : ℕ) :
    x = ∑ j ∈ Finset.range (J + 1), T.ξExt ξ ρ0 ^ j *
        T.liftExt ρ0 (T.divStep hξ hr (T.tay hξ hr x j)).z (T.divStep hξ hr (T.tay hξ hr x j)).hV +
      T.ξExt ξ ρ0 ^ (J + 1) * T.tay hξ hr x (J + 1) := by
  induction J with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      tay_succ]
    exact (T.divStep hξ hr (T.tay hξ hr x 0)).eq
  | succ J ih =>
    rw [Finset.sum_range_succ, T.tay_succ hξ hr x (J + 1)]
    have e := (T.divStep hξ hr (T.tay hξ hr x (J + 1))).eq
    conv_lhs => rw [ih]
    conv_lhs => rw [e]
    ring

variable {hξ hr}

theorem norm_ptEval_le_r (y : T.RobbaExt ρ0) :
    ‖T.ptEval hξ hr y‖ ≤ T.extNorm ρ0 (T.ptRadIoc hξ hr) y := T.norm_ptEval_le hξ hr y

theorem extNorm_next (y : T.RobbaExt ρ0) (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (y - T.liftExt ρ0 (T.divStep hξ hr y).z (T.divStep hξ hr y).hV) =
      max (T.ptRad ξ) σ * T.extNorm ρ0 σ (T.divStep hξ hr y).next := by
  have e : y - T.liftExt ρ0 (T.divStep hξ hr y).z (T.divStep hξ hr y).hV =
      T.ξExt ξ ρ0 * (T.divStep hξ hr y).next := sub_eq_iff_eq_add'.2 (T.divStep hξ hr y).eq
  rw [e, extNorm_mul, T.extNorm_ξExt hξ]

theorem extNorm_next_le (y : T.RobbaExt ρ0) :
    T.ptRad ξ * T.extNorm ρ0 (T.ptRadIoc hξ hr) (T.divStep hξ hr y).next ≤
      T.extNorm ρ0 (T.ptRadIoc hξ hr) y := by
  have h := T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)
  rw [show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self] at h
  rw [← h, sub_eq_add_neg]
  refine (T.extNorm_add_le _ _ _).trans (max_le le_rfl ?_)
  rw [extNorm_neg, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]
  exact T.norm_ptEval_le hξ hr y

theorem extNorm_next_eq (y : T.RobbaExt ρ0)
    (hlt : ‖T.ptEval hξ hr y‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr) y) :
    T.ptRad ξ * T.extNorm ρ0 (T.ptRadIoc hξ hr) (T.divStep hξ hr y).next =
      T.extNorm ρ0 (T.ptRadIoc hξ hr) y := by
  have h := T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)
  rw [show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self] at h
  rw [← h]
  refine T.extNorm_eq_of_lt ?_
  rw [sub_sub_cancel, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]
  exact hlt

end Taylor

section NonDeg

variable {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0)

theorem exists_nbhd_gt {y : T.RobbaExt ρ0} {c : ℝ}
    (hc : c < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) y) :
    ∃ η > 0, T.ptRad ξ + η ≤ ρ0 ∧ ∀ σ : Set.Ioc (0 : ℝ) ρ0, T.ptRad ξ ≤ σ →
      (σ : ℝ) ≤ T.ptRad ξ + η → c < T.extNorm ρ0 σ y := by
  have hr0 := T.ptRad_pos' hξ
  set a : Set.Ioc (0 : ℝ) ρ0 := T.ptRadIoc hξ hr.le
  set b : Set.Ioc (0 : ℝ) ρ0 := ⟨(T.ptRad ξ + ρ0) / 2, by linarith, by linarith⟩
  have hab : (a : ℝ) ≤ b := by show T.ptRad ξ ≤ (T.ptRad ξ + ρ0) / 2; linarith
  have hcont := T.continuousOn_normR y a b
  have hmem : (a : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨le_rfl, hab⟩
  have hca : c < T.normR y a := by rw [T.normR_eq]; exact hc
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont a hmem) (T.normR y a - c)
    (by linarith)
  refine ⟨min (δ / 2) ((ρ0 - T.ptRad ξ) / 2), lt_min (by linarith) (by linarith),
    by linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)], fun σ h1 h2 => ?_⟩
  have hσ : (σ : ℝ) ∈ Set.Icc (a : ℝ) b :=
    ⟨h1, by show (σ : ℝ) ≤ (T.ptRad ξ + ρ0) / 2; linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]⟩
  have hd : dist (σ : ℝ) a < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by show (0:ℝ) ≤ σ - T.ptRad ξ; linarith)]
    show (σ : ℝ) - T.ptRad ξ < δ
    linarith [min_le_left (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]
  have := hδ' hσ hd
  rw [Real.dist_eq, T.normR_eq y σ] at this
  have := neg_abs_le (T.extNorm ρ0 σ y - T.normR y a)
  linarith

theorem mult_next {y : T.RobbaExt ρ0} (hy : y ≠ 0)
    (hlt : ‖T.ptEval hξ hr.le y‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) y) :
    (T.divStep hξ hr.le y).next ≠ 0 ∧
      T.mult (T.divStep hξ hr.le y).next (T.ptRad ξ) = T.mult y (T.ptRad ξ) - 1 := by
  set D := T.divStep hξ hr.le y
  have hlift : ∀ σ, T.extNorm ρ0 σ (T.liftExt ρ0 D.z D.hV) = ‖T.ptEval hξ hr.le y‖ := fun σ => by
    rw [T.extNorm_liftExt _ _ D.hred, D.hz]
  have e : y - T.liftExt ρ0 D.z D.hV = T.ξExt ξ ρ0 * D.next := sub_eq_iff_eq_add'.2 D.eq
  have hnext : D.next ≠ 0 := by
    intro h0
    have hyl : y = T.liftExt ρ0 D.z D.hV := by rw [← sub_eq_zero, e, h0, mul_zero]
    have h3 := hlift (T.ptRadIoc hξ hr.le)
    rw [← hyl] at h3
    rw [h3] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hnext, ?_⟩
  obtain ⟨η, hη, hηle, hηgt⟩ := T.exists_nbhd_gt (hξ := hξ) hr hlt
  have hh : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0 := ⟨T.ptRad_pos' hξ, hr⟩
  obtain ⟨h1, h2⟩ := T.idx_eq_of_near hy hh hη hηle (y' := y - T.liftExt ρ0 D.z D.hV)
    fun σ hσ1 hσ2 => by
      rw [sub_sub_cancel, hlift]
      exact hηgt σ hσ1 hσ2
  have hm1 : T.mult y (T.ptRad ξ) = T.mult (y - T.liftExt ρ0 D.z D.hV) (T.ptRad ξ) := by
    rw [mult, mult, h1, h2]
  rw [hm1, e, T.mult_mul (T.ξExt_ne_zero hξ) hnext hh, T.mult_ξExt hξ hr]
  ring

theorem exists_nondeg {x : T.RobbaExt ρ0} (hx : x ≠ 0) :
    ∃ J : ℕ, (J : ℤ) ≤ T.mult x (T.ptRad ξ) ∧
      (∀ j ≤ J, T.tay hξ hr.le x j ≠ 0 ∧
        T.ptRad ξ ^ j * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j) =
          T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x) ∧
      (∀ j < J, ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖ <
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j)) ∧
      ‖T.ptEval hξ hr.le (T.tay hξ hr.le x J)‖ =
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x J) := by
  classical
  set N := fun j => T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j)
  set v := fun j => ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖
  have hle : ∀ j, v j ≤ N j := fun j => T.norm_ptEval_le hξ hr.le _

  have hind : ∀ J, (∀ j < J, v j < N j) → ∀ j ≤ J, T.tay hξ hr.le x j ≠ 0 ∧
      T.mult (T.tay hξ hr.le x j) (T.ptRad ξ) = T.mult x (T.ptRad ξ) - j ∧
      T.ptRad ξ ^ j * N j = N 0 := by
    intro J hJ j hj
    induction j with
    | zero => exact ⟨hx, by simp [tay_zero], by simp [N]⟩
    | succ j ih =>
      obtain ⟨h0, hm, hn⟩ := ih (by omega)
      have hlt := hJ j (by omega)
      obtain ⟨h0', hm'⟩ := T.mult_next (hξ := hξ) hr h0 hlt
      refine ⟨by rw [tay_succ]; exact h0', by rw [tay_succ, hm', hm]; push_cast; ring, ?_⟩
      have := T.extNorm_next_eq (hξ := hξ) (hr := hr.le) _ hlt
      rw [← hn, pow_succ]
      simp only [N, tay_succ]
      rw [mul_assoc, this]
  have hex : ∃ J, ¬ (v J < N J) := by
    by_contra hcon
    push_neg at hcon
    set M := (T.mult x (T.ptRad ξ)).toNat
    obtain ⟨-, hm, -⟩ := hind (M + 1) (fun j _ => hcon j) (M + 1) le_rfl
    have := T.mult_nonneg (T.tay hξ hr.le x (M + 1)) (T.ptRad ξ)
    have hM : (M : ℤ) = T.mult x (T.ptRad ξ) := Int.toNat_of_nonneg (T.mult_nonneg x _)
    rw [hm] at this
    push_cast at this
    omega
  set J := Nat.find hex
  have hJmin : ∀ j < J, v j < N j := fun j hj => by
    have := Nat.find_min hex hj; push_neg at this; exact this
  have hJ := Nat.find_spec hex
  obtain ⟨-, hmJ, -⟩ := hind J hJmin J le_rfl
  refine ⟨J, ?_, fun j hj => ⟨(hind J hJmin j hj).1, (hind J hJmin j hj).2.2⟩, hJmin,
    le_antisymm (hle J) (not_lt.1 hJ)⟩
  have := T.mult_nonneg (T.tay hξ hr.le x J) (T.ptRad ξ)
  rw [hmJ] at this
  omega

end NonDeg

section Move

theorem ultra_norm_sub_eq_left {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {a b : E} (h : ‖b‖ < ‖a‖) : ‖a - b‖ = ‖a‖ := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact h.ne'),
    norm_neg, max_eq_left h.le]

include hξ in
theorem norm_teich_le_one_of_lt {s : L} (hs : ‖s‖ < T.ptRad ξ) : ‖s‖ ≤ 1 :=
  (hs.trans (T.ptRad_lt_one' hξ)).le

include hξ in

def movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.int := ξ - T.teichInt (T.norm_teich_le_one_of_lt hξ hs)

theorem coe_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : (T.movePt hξ hs : Γ) = ξ - T.teich s := rfl

theorem coeff_zero_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) :
    T.coeff (T.movePt hξ hs : Γ) 0 = T.coeff (ξ : Γ) 0 - s := by
  rw [coe_movePt, coeff_zero, coeff_zero, map_sub, red_teich]

theorem ptRad_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.ptRad (T.movePt hξ hs) = T.ptRad ξ := by
  show ‖T.coeff (T.movePt hξ hs : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖
  rw [coeff_zero_movePt]
  exact ultra_norm_sub_eq_left hs

theorem isPrimOne_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.IsPrimOne (T.movePt hξ hs) where
  coeff_zero_ne := by
    intro h0
    have := T.ptRad_movePt hξ hs
    rw [ptRad, h0, norm_zero] at this
    exact (T.ptRad_pos' hξ).ne this
  norm_coeff_zero_lt := by
    have := T.ptRad_movePt hξ hs
    rw [ptRad] at this
    rw [this]; exact T.ptRad_lt_one' hξ
  norm_coeff_one := by
    have hs1 : ‖s‖ < 1 := hs.trans (T.ptRad_lt_one' hξ)
    have hx : T.PrefixLe (ξ : Γ) 1 1 := fun m _ => T.mem_int_iff.1 ξ.2 m
    have hy : T.PrefixLe (-T.teich s) 1 ‖s‖ := T.prefixLe_neg (T.prefixLe_teich' s 1 le_rfl)
    have h := T.norm_coeff_add_sub_le 1 (norm_nonneg s) hs1.le hx hy 1 le_rfl
    rw [Real.one_rpow, one_mul, ← sub_eq_add_neg] at h
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) 1
    have hlt : ‖s‖ ^ coeffHolderExp p 1 < 1 := Real.rpow_lt_one (norm_nonneg _) hs1 ht0
    have e1 : ‖T.coeff (ξ : Γ) 1‖ = 1 := hξ.norm_coeff_one
    rw [coe_movePt]
    have := ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1)
      (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - T.teich s) 1) (by
        rw [norm_sub_rev, e1]; exact h.trans_lt hlt)
    rw [sub_sub_cancel, e1] at this
    exact this

theorem ptEval_coe_algebraMap {η : T.int} (hη : T.IsPrimOne η) {ρ0 : Set.Ioo (0 : ℝ) 1}
    (hr : T.ptRad η ≤ ρ0) {X : Γ} (hX : algebraMap Γ T.B X ∈ T.Econ ρ0) :
    T.ptEval hη hr ((⟨algebraMap Γ T.B X, hX⟩ : T.Econ ρ0) : T.RobbaExt ρ0) = T.ptE hη X := by
  rw [ptEval_coe]
  exact T.ptEvalB_algebraMap hη X

theorem ptEval_ξExt_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) {ρ0 : Set.Ioo (0 : ℝ) 1}
    (hr : T.ptRad (T.movePt hξ hs) ≤ ρ0) :
    T.ptEval (T.isPrimOne_movePt hξ hs) hr (T.ξExt ξ ρ0) = T.ptSharp (T.isPrimOne_movePt hξ hs) s := by
  set hη := T.isPrimOne_movePt hξ hs
  rw [ξExt, T.ptEval_coe_algebraMap hη hr]
  have hr0 := T.ptRad_pos' hη
  have hr1 := T.ptRad_lt_one' hη
  have e : (ξ : Γ) = (T.movePt hξ hs : Γ) + T.teich s := by rw [coe_movePt]; ring
  rw [e, T.ptE_add hη (T.convergesAt_of_mem_int (T.movePt hξ hs).2 hr0 hr1) (T.convergesAt_teich s _),
    T.ptE_ξ hη, ptE_teich, zero_add]

end Move

section Step

theorem norm_ptE_sub_sharp_red_le {V : Γ} (hV : V ∈ T.int) :
    ‖T.ptE hξ V - T.ptSharp hξ (T.red V)‖ ≤ T.ptRad ξ := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have ht := T.tail_mem_int hV
  have htc := T.convergesAt_of_mem_int ht hr0 hr1
  have hc1 : ConvergesAt (T.zcoeff (T.teich (T.red V))) (T.ptRad ξ) := T.convergesAt_teich _ _
  have hc2 : ConvergesAt (T.zcoeff (T.π * T.tail V)) (T.ptRad ξ) :=
    T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc
  have e : T.ptE hξ V = T.ptSharp hξ (T.red V) + T.ptPi hξ * T.ptE hξ (T.tail V) := by
    conv_lhs => rw [T.eq_teich_add_π_mul_tail V]
    rw [T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]
  rw [e, add_sub_cancel_left, norm_mul, norm_ptPi]
  have h1 : ‖T.ptE hξ (T.tail V)‖ ≤ 1 :=
    (T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)
  calc ‖T.coeff (ξ : Γ) 0‖ * ‖T.ptE hξ (T.tail V)‖ ≤ ‖T.coeff (ξ : Γ) 0‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = T.ptRad ξ := mul_one _

theorem norm_finset_sum_le_ultra {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {ι : Type*} (s : Finset ι) (f : ι → E) {M : ℝ} (hM0 : 0 ≤ M) (h : ∀ i ∈ s, ‖f i‖ ≤ M) :
    ‖∑ i ∈ s, f i‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0)

theorem step_estimate {x : T.RobbaExt ρ0} (hx : x ≠ 0) (hε0 : T.ptEval hξ hr.le x ≠ 0)
    (hεN : ‖T.ptEval hξ hr.le x‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x) :
    ∃ (s : L) (hs : ‖s‖ < T.ptRad ξ) (J : ℕ), 1 ≤ J ∧ (J : ℤ) ≤ T.mult x (T.ptRad ξ) ∧
      (‖s‖ / T.ptRad ξ) ^ J ≤
        ‖T.ptEval hξ hr.le x‖ / T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x ∧
      ‖T.ptEval (T.isPrimOne_movePt hξ hs) ((T.ptRad_movePt hξ hs).trans_le hr.le) x‖ ≤
        ‖T.ptEval hξ hr.le x‖ * max (T.ptRad ξ) (‖s‖ / T.ptRad ξ) := by
  classical
  obtain ⟨J, hJm, hpos, hstrict, hJeq⟩ := T.exists_nondeg (hξ := hξ) hr hx
  set r := T.ptRad ξ with hrdef
  have hr0 : 0 < r := T.ptRad_pos' hξ
  have hr1 : r < 1 := T.ptRad_lt_one' hξ
  set ε := ‖T.ptEval hξ hr.le x‖ with hεdef
  set N := T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x with hNdef
  have hεpos : 0 < ε := norm_pos_iff.2 hε0
  have hNpos : 0 < N := hεpos.trans hεN
  set D := fun j => T.divStep hξ hr.le (T.tay hξ hr.le x j)
  set b : ℕ → L := fun j => (D j).z * T.red (D j).V with hbdef
  have hnb : ∀ j, ‖b j‖ = ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖ := fun j => by
    simp only [hbdef, norm_mul, (D j).hred, mul_one, (D j).hz]
  have hJ1 : 1 ≤ J := by
    by_contra h
    push_neg at h
    have hJ0 : J = 0 := by omega
    rw [hJ0, tay_zero] at hJeq
    have hεN' : ε = N := hJeq
    linarith
  have hb0 : ‖b 0‖ = ε := by rw [hnb, tay_zero]
  have hbJ : r ^ J * ‖b J‖ = N := by rw [hnb, hJeq]; exact (hpos J le_rfl).2

  set g : Polynomial L := ∑ j ∈ Finset.range (J + 1), Polynomial.C (b j) * Polynomial.X ^ j
    with hgdef
  have hcoeff : ∀ k, g.coeff k = if k < J + 1 then b k else 0 := fun k => by
    rw [hgdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (J + 1)) k (fun j => b j)]
    simp [Finset.mem_range]
  have hbJne : b J ≠ 0 := by
    intro h0; rw [h0, norm_zero, mul_zero] at hbJ; exact hNpos.ne hbJ
  have hdeg : g.natDegree = J := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff, if_pos (by omega)]; exact hbJne)
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.1 hj; omega
  have hg0 : g.coeff 0 ≠ 0 := by
    rw [hcoeff, if_pos (by omega)]; intro h0; rw [h0, norm_zero] at hb0; exact hεpos.ne hb0
  obtain ⟨s, hroot, hsj⟩ := exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < g.natDegree) hg0
  have hsj' : ∀ j ≤ J, ‖s‖ ^ j * ‖b j‖ ≤ ε := fun j hj => by
    have := hsj j
    rwa [hcoeff, if_pos (by omega), hcoeff, if_pos (by omega), hb0] at this
  have hratio : (‖s‖ / r) ^ J ≤ ε / N := by
    have := hsj' J le_rfl
    rw [div_pow, div_le_div_iff₀ (pow_pos hr0 J) hNpos, ← hbJ]
    nlinarith [pow_pos hr0 J, norm_nonneg (b J)]
  have hεN1 : ε / N < 1 := (div_lt_one hNpos).2 hεN
  have hsr : ‖s‖ / r < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := J) h
    linarith
  have hs : ‖s‖ < r := by rwa [div_lt_one hr0] at hsr
  refine ⟨s, hs, J, hJ1, hJm, hratio, ?_⟩

  set hη := T.isPrimOne_movePt hξ hs
  have hrη : T.ptRad (T.movePt hξ hs) ≤ ρ0 := (T.ptRad_movePt hξ hs).trans_le hr.le
  have hrad : T.ptRad (T.movePt hξ hs) = r := T.ptRad_movePt hξ hs
  set θ := T.ptEval hη hrη
  have hθξ : θ (T.ξExt ξ ρ0) = T.ptSharp hη s := T.ptEval_ξExt_movePt hξ hs hrη
  have hlift : ∀ j, θ (T.liftExt ρ0 (D j).z (D j).hV) =
      T.ptSharp hη ((D j).z) * T.ptE hη (D j).V := fun j => T.ptEval_liftExt hη hrη _ _
  have hexp := congrArg θ (T.taylor_eq hξ hr.le x J)
  rw [map_add, map_sum] at hexp
  simp only [map_mul, map_pow, hθξ, hlift] at hexp

  set a : ℕ → L := fun j => s ^ j * b j
  have ha : ∀ j ∈ Finset.range (J + 1), ‖a j‖ ≤ ε := fun j hj => by
    simp only [a, norm_mul, norm_pow]; exact hsj' j (by have := Finset.mem_range.1 hj; omega)
  have hsum0 : ∑ j ∈ Finset.range (J + 1), a j = 0 := by
    have := hroot
    rw [Polynomial.IsRoot, hgdef, Polynomial.eval_finset_sum] at this
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a]; ring
  have hA : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j)‖ ≤ r * ε := by
    have := T.norm_sum_sharp_sub_le hη (Finset.range (J + 1)) a hεpos.le ha
    rwa [hsum0, map_zero, sub_zero, hrad] at this
  have hB : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j *
      (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)))‖ ≤ r * ε := by
    refine norm_finset_sum_le_ultra _ _ (by positivity) fun j hj => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_ptSharp, norm_ptSharp]
    have h1 := T.norm_ptE_sub_sharp_red_le hη (D j).hV
    rw [hrad] at h1
    have h2 : ‖s‖ ^ j * ‖(D j).z‖ ≤ ε := by
      have := ha j hj
      simp only [a, b, norm_mul, norm_pow, (D j).hred, mul_one] at this
      exact this
    calc ‖s‖ ^ j * (‖(D j).z‖ * ‖T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)‖)
        = (‖s‖ ^ j * ‖(D j).z‖) * ‖T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)‖ := by ring
      _ ≤ ε * r := mul_le_mul h2 h1 (norm_nonneg _) hεpos.le
      _ = r * ε := mul_comm _ _
  have hIoc : T.ptRadIoc hη hrη = T.ptRadIoc hξ hr.le := Subtype.ext hrad
  have hC : ‖T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1))‖ ≤ ε * (‖s‖ / r) := by
    rw [norm_mul, norm_pow, norm_ptSharp]
    have h1 : ‖θ (T.tay hξ hr.le x (J + 1))‖ ≤
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) := by
      have := T.norm_ptEval_le hη hrη (T.tay hξ hr.le x (J + 1))
      rwa [hIoc] at this
    have h2 : r ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤ N := by
      have := T.extNorm_next_le (hξ := hξ) (hr := hr.le) (T.tay hξ hr.le x J)
      rw [← tay_succ] at this
      rw [pow_succ, ← (hpos J le_rfl).2]
      nlinarith [pow_pos hr0 J]
    have h3 : ‖s‖ ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤
        (‖s‖ / r) ^ (J + 1) * N := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 _)]
      nlinarith [pow_nonneg (norm_nonneg s) (J + 1)]
    calc ‖s‖ ^ (J + 1) * ‖θ (T.tay hξ hr.le x (J + 1))‖
        ≤ ‖s‖ ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (‖s‖ / r) ^ (J + 1) * N := h3
      _ = (‖s‖ / r) * ((‖s‖ / r) ^ J * N) := by ring
      _ ≤ (‖s‖ / r) * ((ε / N) * N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hratio hNpos.le) (by positivity)
      _ = ε * (‖s‖ / r) := by field_simp

  have hsplit : θ x = ∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j) +
      ∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j *
        (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V))) +
      T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1)) := by
    rw [hexp, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hl := hlift j
    simp only [D] at hl
    rw [hl]
    simp only [a, b, D, map_mul, map_pow]
    ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact hA.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)
    · exact hB.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)
  · exact hC.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hεpos.le)

end Step

end TeichLift

end GroundTheory.PAdicHodge

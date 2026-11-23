import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaPointEval
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ξ : T.int} (hξ : T.IsPrimOne ξ)

theorem exists_lift_value {w : T.UntiltField hξ} (hw : ‖w‖ ≤ 1) :
    ∃ z : L, ‖z‖ = ‖w‖ ∧ ∃ V ∈ T.int, T.ptE hξ (T.teich z * V) = w := by
  by_cases hw0 : w = 0
  · refine ⟨0, by rw [hw0, norm_zero, norm_zero], 0, T.int.zero_mem, ?_⟩
    rw [mul_zero, ptE_zero, hw0]
  obtain ⟨q, rfl⟩ := T.exists_toUntiltField_eq hξ hw
  have hq0 : q ≠ 0 := by rintro rfl; exact hw0 (map_zero _)
  obtain ⟨z, hz0, hz, u, hu, hqu⟩ := T.exists_teich_mul_unit hξ hq0
  obtain ⟨U, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hmem : T.teich z * (U : Γ) ∈ T.int := T.int.mul_mem (T.teich_mem_int hz) U.2
  refine ⟨z, ?_, U, U.2, ?_⟩
  · rw [norm_toUntiltField, hqu, T.untiltNorm_mul hξ, T.untiltNorm_teich hξ hz,
      T.untiltNorm_unit hξ hu, mul_one]
  · rw [T.ptE_int hξ hmem, hqu]
    congr 1

theorem gaussNorm_teich_mul_int_le {z : L} {V : Γ} (hV : V ∈ T.int) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) : gaussNorm (T.zcoeff (T.teich z * V)) ρ ≤ ‖z‖ := by
  rw [T.gaussNorm_zcoeff_mul hρ0 hρ1 (T.convergesAt_teich z ρ) (T.convergesAt_of_mem_int hV hρ0 hρ1),
    T.gaussNorm_teich z hρ0]
  exact mul_le_of_le_one_right (norm_nonneg _) (T.gaussNorm_le_one_of_mem_int hV hρ0 hρ1.le)

theorem exists_eq_ξ_mul_of_ptE_eq_zero {W : Γ} (hW : T.IsBddElt W) (h0 : T.ptE hξ W = 0) :
    ∃ Y : Γ, T.IsBddElt Y ∧ W = ξ * Y := by
  obtain ⟨d, hd0, hd1, hdW⟩ := hW
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hWc := T.convergesAt_of_isBddElt ⟨d, hd0, hd1, hdW⟩ hr0 hr1
  have h1 := T.ptE_teich_mul hξ d W hWc
  rw [h0, mul_zero, T.ptE_int hξ hdW] at h1
  have h2 : T.toUntilt ξ ⟨T.teich d * W, hdW⟩ = 0 := by
    rw [← T.untiltNorm_eq_zero_iff hξ, ← norm_toUntiltField, h1, norm_zero]
  obtain ⟨B, hB, hBe⟩ := (T.toUntilt_eq_zero_iff).1 h2
  have hdinv : T.teich d⁻¹ * T.teich d = 1 := by rw [← T.teich_mul, inv_mul_cancel₀ hd0, T.teich_one]
  refine ⟨T.teich d⁻¹ * B, ⟨d, hd0, hd1, ?_⟩, ?_⟩
  · rw [← mul_assoc, mul_comm (T.teich d), hdinv, one_mul]; exact hB
  · have : W = T.teich d⁻¹ * (T.teich d * W) := by rw [← mul_assoc, hdinv, one_mul]
    rw [this]
    change T.teich d⁻¹ * (T.teich d * W) = ξ * (T.teich d⁻¹ * B)
    rw [show T.teich d * W = (ξ : Γ) * B from hBe]; ring

def bddB (U : Γ) (N : ℕ) : T.B := algebraMap Γ T.B U * IsLocalization.Away.invSelf T.π ^ N

theorem bddB_mul_pow (U : Γ) (N : ℕ) :
    T.bddB U N * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B U := by
  rw [bddB, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf T.π),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem bddB_mem_Econ {U : Γ} (hU : T.IsBddElt U) (N : ℕ) (ρ : Set.Ioo (0 : ℝ) 1) :
    T.bddB U N ∈ T.Econ ρ := by
  rw [mem_Econ, T.coeffB_eq (T.bddB_mul_pow U N), convergesAt_shift_iff ρ.2.1]
  exact T.convergesAt_of_isBddElt hU ρ.2.1 ρ.2.2

theorem ptEvalB_bddB (U : Γ) (N : ℕ) :
    T.ptEvalB hξ (T.bddB U N) = T.ptPi hξ ^ (-(N : ℤ)) * T.ptE hξ U :=
  T.ptEvalB_eq hξ (T.bddB_mul_pow U N)

theorem ptE_π_pow (N : ℕ) : T.ptE hξ (T.π ^ N) = T.ptPi hξ ^ N := by
  have hmem : T.π ^ N ∈ T.int := T.int.pow_mem T.π_mem_int N
  rw [T.ptE_int hξ hmem]
  rw [show (⟨T.π ^ N, hmem⟩ : T.int) = T.πInt ^ N from Subtype.ext (by simp [coe_πInt]), map_pow,
    map_pow]
  rfl

theorem exists_bddB_eq_ξ_mul_add {U : Γ} (hU : T.IsBddElt U) (N : ℕ)
    (hw : ‖T.ptEvalB hξ (T.bddB U N)‖ ≤ 1) :
    ∃ Y : Γ, T.IsBddElt Y ∧ ∃ z : L, ‖z‖ = ‖T.ptEvalB hξ (T.bddB U N)‖ ∧ ∃ V ∈ T.int,
      T.bddB U N = algebraMap Γ T.B ξ * T.bddB Y N + algebraMap Γ T.B (T.teich z * V) := by
  obtain ⟨z, hz, V, hV, hzV⟩ := T.exists_lift_value hξ hw
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hzVint : T.teich z * V ∈ T.int := by
    have hz1 : ‖z‖ ≤ 1 := hz ▸ hw
    exact T.int.mul_mem (T.teich_mem_int hz1) hV
  have hπint : T.π ^ N * (T.teich z * V) ∈ T.int := T.int.mul_mem (T.int.pow_mem T.π_mem_int N) hzVint
  have hbdd1 : T.IsBddElt (T.π ^ N * (T.teich z * V)) :=
    ⟨1, one_ne_zero, by simp, by rw [T.teich_one, one_mul]; exact hπint⟩
  have hW : T.IsBddElt (U - T.π ^ N * (T.teich z * V)) := hU.sub T hbdd1
  have hUc := T.convergesAt_of_isBddElt hU hr0 hr1
  have h1c := T.convergesAt_of_isBddElt hbdd1 hr0 hr1
  have hW0 : T.ptE hξ (U - T.π ^ N * (T.teich z * V)) = 0 := by
    rw [sub_eq_add_neg, T.ptE_add hξ hUc (T.convergesAt_zcoeff_neg hr0 hr1 h1c), T.ptE_neg hξ h1c,
      T.ptE_mul hξ (T.convergesAt_of_mem_int (T.int.pow_mem T.π_mem_int N) hr0 hr1)
        (T.convergesAt_of_mem_int hzVint hr0 hr1), ptE_π_pow, hzV, T.ptEvalB_bddB hξ U N]
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (T.ptPi_ne_zero hξ), add_neg_cancel, zpow_zero,
      one_mul, add_neg_cancel]
  obtain ⟨Y, hY, hWY⟩ := T.exists_eq_ξ_mul_of_ptE_eq_zero hξ hW hW0
  refine ⟨Y, hY, z, hz, V, hV, ?_⟩

  have hπ : IsUnit (algebraMap Γ T.B T.π ^ N) := (IsLocalization.Away.algebraMap_isUnit T.π).pow N
  refine hπ.mul_left_injective ?_
  simp only
  rw [T.bddB_mul_pow, add_mul, mul_assoc, T.bddB_mul_pow, ← map_mul, ← map_pow, ← map_mul,
    ← map_add, ← hWY]
  congr 1; ring

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

theorem exists_bdd_approx (x : T.RobbaExt ρ0) (σ : Set.Ioc (0 : ℝ) ρ0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (U : Γ) (hU : T.IsBddElt U), ∀ ρ : Set.Ioc (0 : ℝ) ρ0, (σ : ℝ) ≤ ρ →
      T.extNorm ρ0 ρ (x - ((⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)) < ε := by
  have hO : {y : T.RobbaExt ρ0 | T.extNorm ρ0 σ (x - y) < ε / 2 ∧
      T.extNorm ρ0 (topRad ρ0) (x - y) < ε / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt ((T.continuous_extNorm _).comp (continuous_const.sub continuous_id))
        continuous_const).inter (isOpen_lt ((T.continuous_extNorm _).comp
          (continuous_const.sub continuous_id)) continuous_const)
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact ⟨by linarith, by linarith⟩
  obtain ⟨b, hb1, hb2⟩ := Completion.denseRange_coe.mem_nhds hO
  have hbρ : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, (σ : ℝ) ≤ ρ → T.extNorm ρ0 ρ (x - b) < ε / 2 := fun ρ h =>
    (T.extNorm_le_max σ (topRad ρ0) ρ h ρ.2.2 _).trans_lt (max_lt hb1 hb2)
  obtain ⟨N, X, hX⟩ := IsLocalization.Away.surj T.π (b : T.B)
  have hXc : ConvergesAt (T.zcoeff X) ρ0 := by
    have := b.2
    rwa [mem_Econ, T.coeffB_eq hX, convergesAt_shift_iff ρ0.2.1] at this
  have hσ0 : 0 < (σ : ℝ) := σ.2.1
  obtain ⟨M, hM⟩ : ∃ M, gaussNorm (T.zcoeff (X - T.partialSum X M)) ρ0 < ε / 2 * (σ : ℝ) ^ N :=
    ((T.tendsto_gaussNorm_sub_partialSum ρ0.2.1 hXc).eventually
      (gt_mem_nhds (by positivity))).exists
  refine ⟨N, T.partialSum X M, T.isBddElt_partialSum X M, fun ρ hρ => ?_⟩
  have hρ0 : 0 < (ρ : ℝ) := ρ.2.1
  set c : T.Econ ρ0 := ⟨T.bddB (T.partialSum X M) N, T.bddB_mem_Econ (T.isBddElt_partialSum X M) N ρ0⟩
  have h2 : T.extNorm ρ0 ρ ((b : T.RobbaExt ρ0) - c) < ε / 2 := by
    rw [← Completion.coe_sub, extNorm_coe]
    have hd : ((b - c : T.Econ ρ0) : T.B) * algebraMap Γ T.B T.π ^ N =
        algebraMap Γ T.B (X - T.partialSum X M) := by
      rw [show ((b - c : T.Econ ρ0) : T.B) = (b : T.B) - T.bddB (T.partialSum X M) N from rfl,
        sub_mul, hX, T.bddB_mul_pow, map_sub]
    rw [T.coeffB_eq hd, gaussNorm_shift hρ0]
    have hmono := T.gaussNorm_mono (x := X - T.partialSum X M) hρ0 ρ.2.2
      (T.convergesAt_sub_partialSum ρ0.2.1 hXc M)
    have hρN : (ρ : ℝ) ^ (-(N : ℤ)) ≤ (σ : ℝ) ^ (-(N : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos hσ0 N) (pow_le_pow_left₀ hσ0.le hρ N)
    calc gaussNorm (T.zcoeff (X - T.partialSum X M)) ρ * (ρ : ℝ) ^ (-(N : ℤ))
        ≤ gaussNorm (T.zcoeff (X - T.partialSum X M)) ρ0 * (σ : ℝ) ^ (-(N : ℤ)) :=
          mul_le_mul hmono hρN (zpow_pos hρ0 _).le (gaussNorm_nonneg ρ0.2.1)
      _ < ε / 2 * (σ : ℝ) ^ N * (σ : ℝ) ^ (-(N : ℤ)) :=
          mul_lt_mul_of_pos_right hM (zpow_pos hσ0 _)
      _ = ε / 2 := by
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hσ0.ne', add_neg_cancel, zpow_zero, mul_one]
  have e : x - (c : T.RobbaExt ρ0) = (x - b) + ((b : T.RobbaExt ρ0) - c) := by ring
  rw [e]
  exact (T.extNorm_add_le _ _ _).trans_lt (max_lt ((hbρ ρ hρ).trans (half_lt_self hε))
    (h2.trans (half_lt_self hε)))

theorem algebraMap_ξ_mem_Econ (ρ0 : Set.Ioo (0 : ℝ) 1) : algebraMap Γ T.B ξ ∈ T.Econ ρ0 := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_of_mem_int ξ.2 ρ0.2.1 ρ0.2.2

def ξExt (ξ : T.int) (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)

theorem ptRad_le_extNorm_ξExt (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.ptRad ξ ≤ T.extNorm ρ0 ρ (T.ξExt ξ ρ0) := by
  rw [ξExt, extNorm_coe]
  show T.ptRad ξ ≤ gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) ρ
  rw [coeffB_algebraMap]
  have := (T.convergesAt_of_mem_int ξ.2 ρ.2.1 (lt_of_le_of_lt ρ.2.2 ρ0.2.2)).le_gaussNorm 0
  have h0 : T.zcoeff (ξ : Γ) 0 = T.coeff (ξ : Γ) 0 := T.zcoeff_natCast _ 0
  rw [zpow_zero, mul_one, h0] at this
  exact this

variable (hr : T.ptRad ξ ≤ ρ0)

theorem ptEval_ξExt : T.ptEval hξ hr (T.ξExt ξ ρ0) = 0 := by
  rw [ξExt, ptEval_coe]
  exact T.ptEvalB_ξ hξ

theorem coe_teich_mul_mem_Econ {z : L} (hz : ‖z‖ ≤ 1) {V : Γ} (hV : V ∈ T.int) :
    algebraMap Γ T.B (T.teich z * V) ∈ T.Econ ρ0 := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_of_mem_int (T.int.mul_mem (T.teich_mem_int hz) hV) ρ0.2.1 ρ0.2.2

theorem ptEval_eq_zero_iff (x : T.RobbaExt ρ0) :
    T.ptEval hξ hr x = 0 ↔ ∃ y, x = T.ξExt ξ ρ0 * y := by
  constructor
  swap
  · rintro ⟨y, hy⟩
    rw [hy, map_mul, T.ptEval_ξExt hξ hr, zero_mul]
  intro hx0
  have hr0 := T.ptRad_pos' hξ

  have key : ∀ j : ℕ, ∃ (N : ℕ) (U : Γ) (hU : T.IsBddElt U), ∀ ρ : Set.Ioc (0 : ℝ) ρ0,
      ((ρ0 : ℝ) / (j + 1)) ≤ ρ → T.extNorm ρ0 ρ
        (x - ((⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)) < 1 / (j + 1) :=
    fun j => T.exists_bdd_approx x ⟨(ρ0 : ℝ) / (j + 1), by have := ρ0.2.1; positivity,
      div_le_self ρ0.2.1.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩ Nat.one_div_pos_of_nat
  choose N U hU hUx using key
  set b : ℕ → T.RobbaExt ρ0 := fun j =>
    ((⟨T.bddB (U j) (N j), T.bddB_mem_Econ (hU j) (N j) ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0) with hbdef
  have hbx : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, Tendsto (fun j => T.extNorm ρ0 ρ (x - b j)) atTop (𝓝 0) := by
    intro ρ
    have hρ0 : 0 < (ρ : ℝ) := ρ.2.1
    obtain ⟨J, hJ⟩ := exists_nat_gt ((ρ0 : ℝ) / ρ)
    refine squeeze_zero' (Eventually.of_forall fun j => T.extNorm_nonneg ρ _) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop J] with j hj
    refine (hUx j ρ ?_).le
    rw [div_le_iff₀ (by positivity)]
    have : (ρ0 : ℝ) / ρ < j + 1 := hJ.trans_le (by exact_mod_cast Nat.le_succ_of_le hj)
    rw [div_lt_iff₀ hρ0] at this
    linarith
  have hbt : Tendsto b atTop (𝓝 x) := T.tendsto_of_extNorm hbx

  set v : ℕ → T.UntiltField hξ := fun j => T.ptEvalB hξ (T.bddB (U j) (N j)) with hvdef
  have hv : Tendsto v atTop (𝓝 0) := by
    have := ((T.continuous_ptEval hξ hr).tendsto x).comp hbt
    rw [hx0] at this
    refine this.congr fun j => ?_
    simp only [Function.comp, hbdef, ptEval_coe, hvdef]
  have hvn := tendsto_zero_iff_norm_tendsto_zero.1 hv
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 (hvn.eventually (ge_mem_nhds one_pos))

  have loc : ∀ j, ∃ (Y : Γ) (hY : T.IsBddElt Y) (e : T.Econ ρ0), J0 ≤ j →
      b j = T.ξExt ξ ρ0 * ((⟨T.bddB Y (N j), T.bddB_mem_Econ hY (N j) ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)
        + (e : T.RobbaExt ρ0) ∧ ∀ ρ, T.extNorm ρ0 ρ (e : T.RobbaExt ρ0) ≤ ‖v j‖ := by
    intro j
    by_cases hj : J0 ≤ j
    · obtain ⟨Y, hY, z, hz, V, hV, hUY⟩ := T.exists_bddB_eq_ξ_mul_add hξ (hU j) (N j) (hJ0 j hj)
      have hz1 : ‖z‖ ≤ 1 := hz ▸ hJ0 j hj
      refine ⟨Y, hY, ⟨_, T.coe_teich_mul_mem_Econ hz1 hV⟩, fun _ => ⟨?_, fun ρ => ?_⟩⟩
      · simp only [hbdef, ξExt]
        rw [← Completion.coe_mul, ← Completion.coe_add]
        congr 1
        exact Subtype.ext hUY
      · rw [extNorm_coe]
        show gaussNorm (T.coeffB (algebraMap Γ T.B (T.teich z * V))) ρ ≤ ‖v j‖
        rw [coeffB_algebraMap, ← hz]
        exact T.gaussNorm_teich_mul_int_le hV ρ.2.1 (lt_of_le_of_lt ρ.2.2 ρ0.2.2)
    · exact ⟨0, ⟨1, one_ne_zero, by simp, by simp [T.int.zero_mem]⟩, 0, fun h => absurd h hj⟩
  choose Y hY e he using loc
  set y : ℕ → T.RobbaExt ρ0 := fun j =>
    ((⟨T.bddB (Y j) (N j), T.bddB_mem_Econ (hY j) (N j) ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0) with hydef

  have hξy : ∀ ρ : Set.Ioc (0 : ℝ) ρ0,
      Tendsto (fun j => T.extNorm ρ0 ρ (x - T.ξExt ξ ρ0 * y j)) atTop (𝓝 0) := by
    intro ρ
    have hmax : Tendsto (fun j => max (T.extNorm ρ0 ρ (x - b j)) ‖v j‖) atTop (𝓝 0) := by
      simpa using (hbx ρ).max hvn
    refine squeeze_zero' (Eventually.of_forall fun j => T.extNorm_nonneg ρ _) ?_ hmax
    filter_upwards [eventually_ge_atTop J0] with j hj
    obtain ⟨hbj, hej⟩ := he j hj
    have : x - T.ξExt ξ ρ0 * y j = (x - b j) + (e j : T.RobbaExt ρ0) := by
      rw [hbj]; simp only [hydef]; ring
    rw [this]
    exact (T.extNorm_add_le _ _ _).trans (max_le_max le_rfl (hej ρ))

  have hcau : CauchySeq y := by
    refine T.cauchySeq_of_extNorm fun ρ ε hε => ?_
    have hεr : 0 < ε * T.ptRad ξ := mul_pos hε hr0
    obtain ⟨J, hJ⟩ := eventually_atTop.1 ((hξy ρ).eventually (gt_mem_nhds hεr))
    refine ⟨J, fun j hj k hk => ?_⟩
    have hjk : T.extNorm ρ0 ρ (T.ξExt ξ ρ0 * (y j - y k)) < ε * T.ptRad ξ := by
      have e2 : T.ξExt ξ ρ0 * (y j - y k) = -(x - T.ξExt ξ ρ0 * y j) + (x - T.ξExt ξ ρ0 * y k) := by ring
      rw [e2]
      refine (T.extNorm_add_le _ _ _).trans_lt (max_lt ?_ (hJ k hk))
      rw [extNorm_neg]; exact hJ j hj
    rw [extNorm_mul] at hjk
    have hξge := T.ptRad_le_extNorm_ξExt (ξ := ξ) ρ
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul hξge hcon hε.le (T.extNorm_nonneg ρ _)
    linarith
  obtain ⟨y₀, hy₀⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨y₀, tendsto_nhds_unique (T.tendsto_of_extNorm hξy) (hy₀.const_mul _)⟩

end TeichLift

end GroundTheory.PAdicHodge

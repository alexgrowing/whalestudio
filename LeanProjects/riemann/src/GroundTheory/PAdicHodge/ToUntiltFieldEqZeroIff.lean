import Mathlib
import GroundTheory.PAdicHodge.CauchySeqOfIncrements
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} [CompleteSpace L]

theorem ptEval_ξExt_eq (Q : T.Pt) (hQ : T.ptRad Q.1 ≤ ρ0) (X : T.int) :
    T.ptEval Q.2 hQ (T.ξExt X ρ0) = T.toUntiltField Q.2 (T.toUntilt Q.1 X) := by
  rw [ξExt, ptEval_coe]
  show T.ptEvalB Q.2 (algebraMap Γ T.B X) = _
  rw [ptEvalB_algebraMap, T.ptE_int Q.2 X.2]

theorem toUntiltField_eq_zero_iff (Q : T.Pt) (q : T.Untilt Q.1) :
    T.toUntiltField Q.2 q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have := congrArg norm h
    rw [norm_zero, T.norm_toUntiltField] at this
    exact (T.untiltNorm_eq_zero_iff Q.2).1 this
  · rintro rfl; exact map_zero _

theorem ξExt_mul_of_eq (P Q : T.Pt) {B : Γ} (hB : B ∈ T.int) (h : (P.1 : Γ) = Q.1 * B) :
    T.ξExt P.1 ρ0 = T.ξExt Q.1 ρ0 *
      ((⟨algebraMap Γ T.B B, T.algebraMap_int_mem_Econ hB ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0) := by
  rw [ξExt, ξExt, ← Completion.coe_mul]
  congr 1
  apply Subtype.ext
  show algebraMap Γ T.B P.1 = algebraMap Γ T.B Q.1 * algebraMap Γ T.B B
  rw [h, map_mul]

theorem ptEval_iff_of_ptEval_ξExt (P Q : T.Pt) (hP : T.ptRad P.1 < ρ0) (hQ : T.ptRad Q.1 < ρ0)
    (h : T.ptEval Q.2 hQ.le (T.ξExt P.1 ρ0) = 0) :
    T.ptRad P.1 = T.ptRad Q.1 ∧
      ∀ z : T.RobbaExt ρ0, T.ptEval P.2 hP.le z = 0 ↔ T.ptEval Q.2 hQ.le z = 0 := by
  rw [T.ptEval_ξExt_eq Q hQ.le, T.toUntiltField_eq_zero_iff] at h
  obtain ⟨B, hB, hPB⟩ := (T.toUntilt_eq_zero_iff (ξ := Q.1)).1 h
  have hPQB := T.ξExt_mul_of_eq (ρ0 := ρ0) P Q hB hPB
  set cB : T.RobbaExt ρ0 := ((⟨algebraMap Γ T.B B, T.algebraMap_int_mem_Econ hB ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0) with hcB
  have hcB0 : cB ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hPQB
    exact T.ptExt_ne_zero P.2 hPQB
  have hQr : 0 < T.ptRad Q.1 ∧ T.ptRad Q.1 < ρ0 := ⟨T.ptRad_pos' Q.2, hQ⟩
  have hm := T.mult_mul (T.ptExt_ne_zero Q.2) hcB0 hQr
  rw [← hPQB, T.mult_ptExt P.2 hQr, T.mult_ptExt Q.2 hQr, if_pos rfl] at hm
  have hr : T.ptRad Q.1 = T.ptRad P.1 := by
    by_contra hne
    rw [if_neg hne] at hm
    have := T.mult_nonneg cB (T.ptRad Q.1)
    omega
  refine ⟨hr.symm, ?_⟩

  have hredB : ‖T.red B‖ = 1 := by
    have e := congrArg T.red hPB
    rw [map_mul] at e
    have e2 := congrArg norm e
    rw [norm_mul, ← coeff_zero, ← coeff_zero] at e2
    have hQ0 : 0 < ‖T.coeff (Q.1 : Γ) 0‖ := T.ptRad_pos' Q.2
    have : ‖T.coeff (P.1 : Γ) 0‖ = ‖T.coeff (Q.1 : Γ) 0‖ := hr.symm
    rw [this] at e2
    field_simp at e2
    linarith [e2]
  have hBu : IsUnit (⟨B, hB⟩ : T.int) := T.isUnit_int_iff.2 hredB
  obtain ⟨Binv, hBinv⟩ := hBu.exists_right_inv
  set cBi : T.RobbaExt ρ0 :=
    ((⟨algebraMap Γ T.B Binv, T.algebraMap_int_mem_Econ Binv.2 ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)
    with hcBi
  have hQP : T.ξExt Q.1 ρ0 = T.ξExt P.1 ρ0 * cBi := by
    refine T.ξExt_mul_of_eq (ρ0 := ρ0) Q P Binv.2 ?_
    have e := congrArg Subtype.val hBinv
    simp only [Subring.coe_mul, Subring.coe_one] at e
    rw [hPB, mul_assoc, e, mul_one]
  intro z
  rw [T.ptEval_eq_zero_iff P.2 hP.le, T.ptEval_eq_zero_iff Q.2 hQ.le]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨cB * y, by rw [hPQB, mul_assoc]⟩
  · rintro ⟨y, rfl⟩; exact ⟨cBi * y, by rw [hQP, mul_assoc]⟩

theorem ptEval_πExt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.πExt ρ0) = T.ptPi P.2 := by
  rw [πExt, ptEval_coe]
  show T.ptEvalB P.2 (algebraMap Γ T.B T.π) = _
  rw [ptEvalB_algebraMap, ← pow_one T.π, T.ptE_π_pow P.2 1, pow_one]

theorem ptEval_πInvExt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.πInvExt ρ0) = (T.ptPi P.2)⁻¹ := by
  have h := congrArg (T.ptEval P.2 hr) (T.πExt_mul_πInvExt ρ0)
  rw [map_mul, map_one, ptEval_πExt] at h
  exact eq_inv_of_mul_eq_one_right h

theorem exists_bezout_pt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) {z : T.RobbaExt ρ0}
    (hz : T.ptEval P.2 hr z ≠ 0) :
    ∃ a b : T.RobbaExt ρ0, a * T.normPtExt P.2 ρ0 + b * z = 1 := by
  set v := (T.ptEval P.2 hr z)⁻¹ with hv
  have hv0 : v ≠ 0 := inv_ne_zero hz
  have hpi : ‖T.ptPi P.2‖ < 1 := by rw [T.norm_ptPi P.2]; exact T.ptRad_lt_one' P.2
  have hpi0 : T.ptPi P.2 ≠ 0 := T.ptPi_ne_zero P.2
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / ‖v‖ by positivity) hpi
  set w := v * T.ptPi P.2 ^ m with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, norm_pow]
    rw [lt_div_iff₀ (norm_pos_iff.2 hv0)] at hm
    linarith [mul_comm ‖v‖ (‖T.ptPi P.2‖ ^ m)]
  obtain ⟨zz, hzz, V, hV, hVe⟩ := T.exists_lift_value P.2 hw1
  have hzz1 : ‖zz‖ ≤ 1 := hzz ▸ hw1
  set b : T.RobbaExt ρ0 := ((⟨algebraMap Γ T.B (T.teich zz * V),
    T.coe_teich_mul_mem_Econ hzz1 hV⟩ : T.Econ ρ0) : T.RobbaExt ρ0) * T.πInvExt ρ0 ^ m with hb
  have hbv : T.ptEval P.2 hr b = v := by
    rw [hb, map_mul, map_pow, ptEval_πInvExt, ptEval_coe]
    show T.ptEvalB P.2 (algebraMap Γ T.B (T.teich zz * V)) * _ = v
    rw [ptEvalB_algebraMap, hVe, hw, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpi0),
      mul_one]
  have h0 : T.ptEval P.2 hr (b * z - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hbv, hv, inv_mul_cancel₀ hz, sub_self]
  obtain ⟨q, hq⟩ := (T.ptEval_eq_zero_iff P.2 hr _).1 h0
  refine ⟨-(T.normUnitInv (ξ := P.1) ρ0 * q), b, ?_⟩
  rw [T.ξExt_eq_normPtExt P.2] at hq
  linear_combination hq

theorem exists_bezout_list (z : T.RobbaExt ρ0) (l : List T.Pt)
    (h : ∀ P ∈ l, ∃ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr z ≠ 0) :
    ∃ a b : T.RobbaExt ρ0, a * T.normProd ρ0 l + b * z = 1 := by
  induction l with
  | nil => exact ⟨1, 0, by rw [normProd_nil]; ring⟩
  | cons P l ih =>
    obtain ⟨hr, hP⟩ := h P List.mem_cons_self
    obtain ⟨a1, b1, h1⟩ := T.exists_bezout_pt P hr hP
    obtain ⟨a2, b2, h2⟩ := ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    refine ⟨a1 * a2, b1 + b2 - b1 * b2 * z, ?_⟩
    rw [normProd_cons]
    linear_combination (a2 * T.normProd ρ0 l) * h1 + (1 - b1 * z) * h2

theorem ptEval_ptProd_eq_zero {l : List T.Pt} (Q : T.Pt) (hQ : T.ptRad Q.1 ≤ ρ0)
    (h : T.ptEval Q.2 hQ (T.ptProd ρ0 l) = 0) : ∃ P ∈ l, T.ptEval Q.2 hQ (T.ξExt P.1 ρ0) = 0 := by
  rw [ptProd, map_list_prod, List.prod_eq_zero_iff, List.map_map] at h
  obtain ⟨P, hP, hP0⟩ := List.mem_map.1 h
  exact ⟨P, hP, hP0⟩

theorem exists_greedy (l : List T.Pt) (hl : ∀ P ∈ l, T.ptRad P.1 < ρ0) (y : T.RobbaExt ρ0) :
    ∃ (R K : List T.Pt) (y'' : T.RobbaExt ρ0),
      y = T.ptProd ρ0 R * y'' ∧ T.ptProd ρ0 l = T.ptProd ρ0 R * T.ptProd ρ0 K ∧
      (∀ P ∈ R, P ∈ l) ∧ (∀ P ∈ K, P ∈ l) ∧
      ∀ P ∈ K, ∀ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr y'' ≠ 0 := by
  induction l generalizing y with
  | nil => exact ⟨[], [], y, by rw [ptProd_nil, one_mul], by simp [ptProd], by simp, by simp, by simp⟩
  | cons P l ih =>
    have hPr := hl P List.mem_cons_self
    have hl' : ∀ Q ∈ l, T.ptRad Q.1 < ρ0 := fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    by_cases h0 : T.ptEval P.2 hPr.le y = 0
    · obtain ⟨y1, hy1⟩ := (T.ptEval_eq_zero_iff P.2 hPr.le y).1 h0
      obtain ⟨R, K, y'', hy, hlRK, hR, hK, hKev⟩ := ih hl' y1
      refine ⟨P :: R, K, y'', ?_, ?_, ?_, fun Q hQ => List.mem_cons_of_mem _ (hK Q hQ), hKev⟩
      · rw [hy1, hy, ptProd_cons, mul_assoc]
      · rw [ptProd_cons, ptProd_cons, hlRK, mul_assoc]
      · intro Q hQ
        rcases List.mem_cons.1 hQ with rfl | hQ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hR Q hQ)
    · obtain ⟨R, K, y'', hy, hlRK, hR, hK, hKev⟩ := ih hl' y
      refine ⟨R, P :: K, y'', hy, ?_, fun Q hQ => List.mem_cons_of_mem _ (hR Q hQ), ?_, ?_⟩
      · rw [ptProd_cons, ptProd_cons, hlRK]; ring
      · intro Q hQ
        rcases List.mem_cons.1 hQ with rfl | hQ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hK Q hQ)
      · intro Q hQ hr
        rcases List.mem_cons.1 hQ with rfl | hQ
        · intro hQ0
          apply h0
          rw [hy, map_mul, hQ0, mul_zero]
        · exact hKev Q hQ hr

theorem exists_stage (hRE : T.RootExists) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < ρ0)
    {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (R : List T.Pt) (x' y' : T.RobbaExt ρ0), x = T.ptProd ρ0 R * x' ∧ y = T.ptProd ρ0 R * y' ∧
      (∀ P ∈ R, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x' ≠ 0 ∧ y' ≠ 0 ∧
      ∀ Q : T.Pt, ∀ hQ : a ≤ T.ptRad Q.1 ∧ T.ptRad Q.1 ≤ b,
        ¬ (T.ptEval Q.2 (hQ.2.trans hb.le) x' = 0 ∧ T.ptEval Q.2 (hQ.2.trans hb.le) y' = 0) := by
  obtain ⟨l, w, hlrad, hxl, hw0, hwm⟩ := T.exists_factor_annulus hRE ha hab hb hx
  obtain ⟨R, K, y'', hy'', hlRK, hR, hK, hKev⟩ :=
    T.exists_greedy l (fun P hP => (hlrad P hP).2.trans_lt hb) y
  refine ⟨R, T.ptProd ρ0 K * w, y'', ?_, hy'', fun P hP => hlrad P (hR P hP),
    mul_ne_zero (T.ptProd_ne_zero K) hw0, ?_, ?_⟩
  · rw [hxl, hlRK, mul_assoc]
  · rintro rfl; rw [mul_zero] at hy''; exact hy hy''
  · rintro Q hQ ⟨hQx, hQy⟩
    have hs : 0 < T.ptRad Q.1 ∧ T.ptRad Q.1 < ρ0 := ⟨ha.trans_le hQ.1, hQ.2.trans_lt hb⟩
    rw [map_mul, mul_eq_zero] at hQx
    rcases hQx with hK0 | hw
    · obtain ⟨P, hP, hP0⟩ := T.ptEval_ptProd_eq_zero Q _ hK0
      have hPr : T.ptRad P.1 < ρ0 := (hlrad P (hK P hP)).2.trans_lt hb
      obtain ⟨-, hiff⟩ := T.ptEval_iff_of_ptEval_ξExt P Q hPr hs.2 hP0
      exact hKev P hP hPr.le ((hiff y'').2 hQy)
    · obtain ⟨w', hw'⟩ := (T.ptEval_eq_zero_iff Q.2 _ w).1 hw
      have hw'0 : w' ≠ 0 := by rintro rfl; rw [mul_zero] at hw'; exact hw0 hw'
      have hm := T.mult_mul (T.ptExt_ne_zero Q.2) hw'0 hs
      rw [← hw', hwm _ hQ.1 hQ.2, T.mult_ptExt Q.2 hs, if_pos rfl] at hm
      have := T.mult_nonneg w' (T.ptRad Q.1)
      omega

structure GcdSt (ρ0 : Set.Ioo (0 : ℝ) 1) where
  x : T.RobbaExt ρ0
  y : T.RobbaExt ρ0
  hx : x ≠ 0
  hy : y ≠ 0

def annLo (ρ0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) : ℝ := (ρ0 : ℝ) / 2 ^ (k + 2)
def annHi (ρ0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) : ℝ := (ρ0 : ℝ) / 2 ^ (k + 1)

theorem annLo_pos (k : ℕ) : 0 < annLo ρ0 k := by unfold annLo; have := ρ0.2.1; positivity

theorem annLo_le (k : ℕ) : annLo ρ0 k ≤ annHi ρ0 k := by
  unfold annLo annHi
  exact div_le_div_of_nonneg_left ρ0.2.1.le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))

theorem annHi_lt (k : ℕ) : annHi ρ0 k < ρ0 := by
  unfold annHi
  rw [div_lt_iff₀ (by positivity)]
  have := ρ0.2.1
  have : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
  nlinarith

theorem annHi_succ (k : ℕ) : annHi ρ0 (k + 1) = annLo ρ0 k := by
  unfold annHi annLo; ring_nf

theorem exists_ann {s : ℝ} (hs0 : 0 < s) (hs : s ≤ (ρ0 : ℝ) / 2) :
    ∃ k, annLo ρ0 k ≤ s ∧ s ≤ annHi ρ0 k := by
  have ht : 1 ≤ (ρ0 : ℝ) / 2 / s := by rw [le_div_iff₀ hs0, one_mul]; exact hs
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ht (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_, ?_⟩
  · unfold annLo
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hs0] at hn2
    have e : s * 2 ^ (n + 2) = 2 * (2 ^ (n + 1) * s) := by ring
    rw [e]; linarith
  · unfold annHi
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hs0] at hn1
    have e : s * 2 ^ (n + 1) = 2 * (2 ^ n * s) := by ring
    rw [e]; linarith

variable (hRE : T.RootExists)
include hRE

def gcdStep (k : ℕ) (S : T.GcdSt ρ0) : List T.Pt × T.GcdSt ρ0 :=
  let h := T.exists_stage hRE (annLo_pos (ρ0 := ρ0) k) (annLo_le k) (annHi_lt k) S.hx S.hy
  (Classical.choose h, ⟨Classical.choose (Classical.choose_spec h),
    Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.2.1,
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.2.2.1⟩)

theorem gcdStep_spec (k : ℕ) (S : T.GcdSt ρ0) :
    S.x = T.ptProd ρ0 (T.gcdStep hRE k S).1 * (T.gcdStep hRE k S).2.x ∧
      S.y = T.ptProd ρ0 (T.gcdStep hRE k S).1 * (T.gcdStep hRE k S).2.y ∧
      (∀ P ∈ (T.gcdStep hRE k S).1, annLo ρ0 k ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ annHi ρ0 k) ∧
      ∀ Q : T.Pt, ∀ hQ : annLo ρ0 k ≤ T.ptRad Q.1 ∧ T.ptRad Q.1 ≤ annHi ρ0 k,
        ¬ (T.ptEval Q.2 (hQ.2.trans (annHi_lt k).le) (T.gcdStep hRE k S).2.x = 0 ∧
          T.ptEval Q.2 (hQ.2.trans (annHi_lt k).le) (T.gcdStep hRE k S).2.y = 0) := by
  have h := T.exists_stage hRE (annLo_pos (ρ0 := ρ0) k) (annLo_le k) (annHi_lt k) S.hx S.hy
  have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.2⟩

def gcdStates (S0 : T.GcdSt ρ0) : ℕ → T.GcdSt ρ0
  | 0 => S0
  | k + 1 => (T.gcdStep hRE k (gcdStates S0 k)).2

def gcdRemoved (S0 : T.GcdSt ρ0) (k : ℕ) : List T.Pt := (T.gcdStep hRE k (T.gcdStates hRE S0 k)).1

theorem gcdStates_spec (S0 : T.GcdSt ρ0) (k : ℕ) :
    S0.x = T.ptProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) * (T.gcdStates hRE S0 k).x ∧
      S0.y = T.ptProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) *
        (T.gcdStates hRE S0 k).y := by
  induction k with
  | zero => simp [gcdStates, ptProd]
  | succ k ih =>
    obtain ⟨hx, hy, -, -⟩ := T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)
    rw [List.range_succ, List.flatMap_append, ptProd_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine ⟨?_, ?_⟩
    · rw [ih.1, hx, mul_assoc]; rfl
    · rw [ih.2, hy, mul_assoc]; rfl

omit hRE in
theorem tendsto_annHi : Tendsto (annHi ρ0) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 < 1 by norm_num)).const_mul ((ρ0 : ℝ) / 2)
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  unfold annHi
  rw [pow_succ, div_pow, one_pow]
  field_simp

omit hRE in
theorem annHi_nonneg (k : ℕ) : 0 ≤ annHi ρ0 k := (annLo_pos k).le.trans (annLo_le k)

theorem exists_gcd {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (d x' y' : T.RobbaExt ρ0), d ≠ 0 ∧ x = d * x' ∧ y = d * y' ∧
      ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
        ¬ (T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) x' = 0 ∧
          T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) y' = 0) := by
  set S0 : T.GcdSt ρ0 := ⟨x, y, hx, hy⟩
  have hl : ∀ k, ∀ P ∈ T.gcdRemoved hRE S0 k, T.ptRad P.1 ≤ annHi ρ0 k := fun k P hP =>
    ((T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.1 P hP).2
  set D := InfProd.ofLists T ρ0 (T.gcdRemoved hRE S0) (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hpart : ∀ k, D.part k = T.normProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) :=
    fun k => InfProd.ofLists_part T _ _ _ _ _ k
  have hdx : ∀ k, D.part k ∣ x := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).1⟩
  have hdy : ∀ k, D.part k ∣ y := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).2⟩
  obtain ⟨x', hx'⟩ := D.dvd_of_forall hdx
  obtain ⟨y', hy'⟩ := D.dvd_of_forall hdy
  refine ⟨D.prod, x', y', D.prod_ne_zero, hx', hy', ?_⟩
  rintro Q hQ ⟨h1, h2⟩
  have hs0 := T.ptRad_pos' Q.2
  obtain ⟨k, hk1, hk2⟩ := exists_ann (ρ0 := ρ0) hs0 hQ
  set F := (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)
  have hQr : T.ptRad Q.1 ≤ ρ0 := hQ.trans (half_le_self ρ0.2.1.le)

  have key : ∀ (w w' W : T.RobbaExt ρ0), w = D.prod * w' → w = T.ptProd ρ0 F * W →
      T.ptEval Q.2 hQr w' = 0 → T.ptEval Q.2 hQr W = 0 := by
    intro w w' W hw hW hw'
    have e : T.ptProd ρ0 F * W = T.ptProd ρ0 F * (T.unitProd ρ0 F * (D.shift (k + 1)).prod * w') := by
      rw [← hW, hw, D.prod_eq_part_mul_shift (k + 1), hpart, normProd_eq]; ring
    have hW' := mul_left_cancel₀ (T.ptProd_ne_zero F) e
    rw [hW', map_mul, hw', mul_zero]
  have hX := key x x' _ hx' (T.gcdStates_spec hRE S0 (k + 1)).1 h1
  have hY := key y y' _ hy' (T.gcdStates_spec hRE S0 (k + 1)).2 h2
  exact (T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.2 Q ⟨hk1, hk2⟩ ⟨hX, hY⟩

end TeichLift

end GroundTheory.PAdicHodge

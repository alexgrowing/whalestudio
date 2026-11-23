import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZerosStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExceptionalPair

theorem one_le_log {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_mul_le {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith

theorem le_log_mul {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)

theorem div_log_le {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]

private theorem exists_ne_zero_smul_mem_of_mem_span' {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    a / y ≤ b / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  nlinarith [mul_le_mul_of_nonneg_right hab hx.le, mul_le_mul_of_nonneg_left hxy (ha.trans hab)]

theorem main : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  obtain ⟨cu, hcu, hU⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨cp, hcp, hP⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  obtain ⟨cz, hcz, hZ⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨cs, hcs, hS⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨min (1 / 8) (min (cu / 2) (cp / 2)),
    lt_min (by norm_num) (lt_min (by linarith) (by linarith)), fun c₁ hc₁ hc₁0 => ?_⟩
  have hc18 : c₁ ≤ 1 / 8 := hc₁0.trans (min_le_left _ _)
  have hcu2 : c₁ ≤ cu / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp2 : c₁ ≤ cp / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c := min c₁ (min cz (min cp (cs / 2))) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (lt_min hcz (lt_min hcp (by linarith)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hccz : c ≤ cz := (min_le_right _ _).trans (min_le_left _ _)
  have hccp : c ≤ cp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccs : c ≤ cs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, fun M _ hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog1 : 1 ≤ Real.log M := one_le_log hM
  have hlogpos : 0 < Real.log M := lt_of_lt_of_le one_pos hlog1
  have hsmall : c₁ / Real.log M ≤ 1 / 8 := (div_le_self hc₁.le hlog1).trans hc18
  have hlogT : ∀ t : ℝ, 0 < Real.log (M * (|t| + 2)) := fun t =>
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hexc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β →
      χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ 1 - cu / Real.log (2 * M) ≤ β := by
    intro χ β h
    obtain ⟨_, hlt, hlt1, hL⟩ := h
    have hβ : 7 / 8 ≤ β := by linarith
    have hne : (β : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hLχ : LFunction χ β = 0 :=
      (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ β (by simp; linarith) (Or.inr hne)).1.mpr hL
    refine ⟨fun hχ => ?_, hβ, hLχ, by linarith [div_log_le hM hcu.le hcu2]⟩
    rw [hχ] at hLχ
    have h1 := hP M (β : ℂ) hne hLχ
    have e : (M : ℝ) * 2 = 2 * M := mul_comm _ _
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add, e] at h1
    linarith [div_log_le hM hcp.le hcp2]
  refine ⟨fun χ χ' β β' h h' => ?_, fun χ β h => ?_, fun χ ρ hre hL => ?_⟩
  · obtain ⟨n1, -, L1, b1⟩ := hexc χ β h
    obtain ⟨n2, -, L2, b2⟩ := hexc χ' β' h'
    obtain ⟨s1, -⟩ := h
    obtain ⟨s2, -⟩ := h'
    obtain ⟨e1, e2, -⟩ := hU M χ χ' β β' n1 n2 s1 s2 b1 b2 L1 L2
    exact ⟨e1, e2⟩
  · obtain ⟨n1, h78, L1, b1⟩ := hexc χ β h
    obtain ⟨s1, -⟩ := h
    refine ⟨n1, h78, L1, ?_, ?_⟩
    · have hd := (hU M χ χ β β n1 n1 s1 s1 b1 b1 L1 L1).2.2
      have h1 := (GlobalTheory.RealZeroNearOne.analyticAt_L n1 (β : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        L1 hd
      rw [GlobalTheory.Lin.ord, analyticOrderNatAt, h1]
      rfl
    · have h1 := hS M χ β (Or.inl n1) L1 (by simp)
      rw [Complex.ofReal_re] at h1
      have hl3 := log_mul_le hM (a := 3) (by norm_num) le_rfl
      have hl3pos : 0 < Real.log (3 * M) := Real.log_pos (by linarith)
      have hD : 0 < (M : ℝ) ^ 2 * Real.log M := by positivity
      have hE : 0 < (M : ℝ) ^ 2 * Real.log (3 * M) := by positivity
      calc c / ((M : ℝ) ^ 2 * Real.log M) ≤ (cs / 2) / ((M : ℝ) ^ 2 * Real.log M) :=
            exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccs hD le_rfl
        _ = cs / (2 * ((M : ℝ) ^ 2 * Real.log M)) := div_div cs 2 _
        _ ≤ cs / ((M : ℝ) ^ 2 * Real.log (3 * M)) :=
            exists_ne_zero_smul_mem_of_mem_span' hcs.le le_rfl hE (by nlinarith [sq_nonneg (M : ℝ)])
        _ ≤ 1 - β := h1
  · by_cases hreal : χ ^ 2 = 1 ∧ ρ.im = 0
    · obtain ⟨hsq, him⟩ := hreal
      have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      by_cases hbig : 1 - c₁ / Real.log M < ρ.re
      · left
        refine ⟨him, ?_⟩
        have hpos : 0 < ρ.re := by linarith
        have hne : ρ ≠ 1 := fun h => by
          rw [h] at hre
          simp at hre
        have hL' := (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ ρ hpos (Or.inr hne)).1.mp hL
        unfold IsExc
        refine ⟨hsq, hbig, hre, ?_⟩
        rw [← hρ]
        exact hL'
      · right
        replace hbig := not_lt.mp hbig
        rw [him, abs_zero, zero_add]
        have h2 : Real.log M ≤ Real.log (M * 2) := by
          rw [mul_comm]
          exact le_log_mul hM (by norm_num)
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hcc₁ hlogpos h2
        linarith
    · right
      have hne' : χ ^ 2 = 1 → ρ.im ≠ 0 := fun h h' => hreal ⟨h, h'⟩
      by_cases hχ : χ = 1
      · have him : ρ.im ≠ 0 := hne' (by rw [hχ]; exact one_pow 2)
        have hne : ρ ≠ 1 := fun h => him (by rw [h]; simp)
        rw [hχ] at hL
        have h1 := hP M ρ hne hL
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccp (hlogT ρ.im) le_rfl
        linarith
      · have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := by
          by_cases h : χ ^ 2 = 1
          · exact Or.inr (hne' h)
          · exact Or.inl h
        have h1 := hZ M χ ρ hχ hL hor
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccz (hlogT ρ.im) le_rfl
        linarith

end GlobalTheory.ExceptionalPair

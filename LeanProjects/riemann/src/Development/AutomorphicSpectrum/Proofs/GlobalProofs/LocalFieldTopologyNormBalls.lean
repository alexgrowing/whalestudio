import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLTop

theorem isOpen_integers (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen ((𝒪[F] : Subring F) : Set F) := by
  refine AddSubgroup.isOpen_of_mem_nhds (𝒪[F] : Subring F).toAddSubgroup (g := 0) ?_
  refine (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mpr ⟨1, one_ne_zero, fun x hx => ?_⟩
  exact (Valuation.mem_integer_iff _ _).mpr (le_of_lt hx)

theorem nrm_le_one_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q) :
    1 < q ∧ ∀ x : F, nrm x ≤ 1 ↔ x ∈ O := by
  have hq : 1 < q := by rw [h.card]; exact Finite.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨hq, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
  have hv0 : 0 < ValuativeRel.valuation F ϖ := zero_lt_iff.mpr (by simpa using h.ne)
  have hx0 : 0 < ValuativeRel.valuation F x := zero_lt_iff.mpr (by simpa using hx)
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hw : 1 < (ValuativeRel.valuation F ϖ)⁻¹ := (one_lt_inv₀ hv0).mpr hv
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (ValuativeRel.valuation F ϖ)⁻¹ ^ n < ValuativeRel.valuation F x ∧
      ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    obtain ⟨a, ha⟩ := exists_pow_lt₀ hv (Units.mk0 _ hx0.ne')
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hv (Units.mk0 _ (inv_pos.mpr hx0).ne')
    simp only [Units.val_mk0] at ha hb
    obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd
      (P := fun z : ℤ => ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ z)
      ⟨-(a : ℤ), fun z hz => by
        have h1 : (ValuativeRel.valuation F ϖ)⁻¹ ^ (-(a : ℤ)) < (ValuativeRel.valuation F ϖ)⁻¹ ^ z := by
          refine lt_of_lt_of_le ?_ hz
          simpa using ha
        exact ((zpow_lt_zpow_iff_right₀ hw).mp h1).le⟩
      ⟨(b : ℤ), by
        rw [zpow_natCast, inv_pow]
        exact ((lt_inv_comm₀ (pow_pos hv0 b) hx0).mp hb).le⟩
    refine ⟨m - 1, ?_, by simpa using hm⟩
    by_contra hc
    have := hmin _ (not_lt.mp hc)
    omega
  rw [_root_.inv_zpow] at hn1 hn2
  have hp : ∀ m : ℤ, 0 < ValuativeRel.valuation F ϖ ^ m := fun m => zpow_pos hv0 m
  have hy : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) = 1 := by
    have hle : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) ≤ 1 := by
      rw [map_mul, map_zpow₀]
      rwa [← one_mul (_ ⁻¹), le_mul_inv_iff₀ (hp _)] at hn2
    by_contra hne
    obtain ⟨o, ho, he⟩ := (h.lt_one _).mp (lt_of_le_of_ne hle hne)
    rw [zpow_add_one₀ h.ne, ← mul_assoc, mul_comm ϖ o] at he
    have he' := mul_right_cancel₀ h.ne he
    rw [← he', h.O_eq, Valuation.mem_integer_iff, map_mul, map_zpow₀] at ho
    rw [← one_mul (_ ⁻¹), mul_inv_lt_iff₀ (hp _)] at hn1
    exact absurd ho (not_le.mpr hn1)
  have hn := h.nrm_unit _ hy
  rw [map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ (by positivity))] at hn
  rw [map_mul, map_zpow₀] at hy
  have hy' : ValuativeRel.valuation F x = (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    rw [_root_.inv_zpow]; exact eq_inv_of_mul_eq_one_left hy
  rw [hn, h.O_eq, Valuation.mem_integer_iff, hy', zpow_le_one_iff_right₀ hq1, zpow_le_one_iff_right₀ hw]

theorem localField_top : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  intro F _ _ _ _ O ϖ nrm q h
  obtain ⟨hq, hle⟩ := nrm_le_one_iff h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
  have hO : IsOpen (O : Set F) := by rw [h.O_eq]; exact isOpen_integers F
  have hball : ∀ (e : ℤ) (x : F), nrm x ≤ (q : ℝ) ^ e ↔ x * ϖ ^ e ∈ O := by
    intro e x
    rw [← hle, map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, ← div_eq_mul_inv, div_le_one (zpow_pos hq0 e)]
  have hopen : ∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e} := by
    intro e
    have : {x : F | nrm x ≤ (q : ℝ) ^ e} = (fun x => x * ϖ ^ e) ⁻¹' (O : Set F) := by
      ext x; exact hball e x
    rw [this]
    exact hO.preimage (continuous_id.mul continuous_const)
  refine ⟨hO, ?_, GlobalTheory.SgLoc.Top.localField_secondCountable F, ?_, hopen, ?_⟩
  · rw [h.O_eq]
    exact IsNonarchimedeanLocalField.isCompact_closedBall F 1
  · rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq1)
    have hU : IsOpen ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) :=
      (hopen _).preimage (continuous_id.sub continuous_const)
    have hm : x₀ ∈ ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) := by
      show nrm (x₀ - x₀) ≤ _
      rw [sub_self, map_zero]; exact (zpow_pos hq0 _).le
    filter_upwards [hU.mem_nhds hm] with x hx
    have hx' : nrm (x - x₀) ≤ (q : ℝ) ^ (-(n : ℤ)) := hx
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at hx'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((nrm.abs_abv_sub_le_abv_sub x x₀).trans hx') hn
  · intro s hs
    obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hs
    have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
    haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hv (Units.mk0 γ hγ)
    refine ⟨-(n : ℤ), fun x hx => hs ?_⟩
    have hx' := (hball _ x).mp hx
    rw [h.O_eq, Valuation.mem_integer_iff] at hx'
    have : x = (x * ϖ ^ (-(n : ℤ))) * ϖ ^ n := by
      rw [_root_.zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h.ne), mul_one]
    show ValuativeRel.valuation F x < γ
    rw [this, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hn

end GlobalTheory.CompanionTheory.QLTop

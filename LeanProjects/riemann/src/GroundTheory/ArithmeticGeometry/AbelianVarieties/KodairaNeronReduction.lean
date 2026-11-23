import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronAdditive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  {π : 𝒪} (hπ : Irreducible π)

local notation "ι" => algebraMap 𝒪 K

instance isIntegral_map : IsIntegral 𝒪 (W.map (algebraMap 𝒪 K)) := ⟨⟨W, rfl⟩⟩

theorem integralModel_map : integralModel 𝒪 (W.map (algebraMap 𝒪 K)) = W := by
  apply WeierstrassCurve.map_injective (IsFractionRing.injective 𝒪 K)
  exact baseChange_integralModel_eq 𝒪 (W.map (algebraMap 𝒪 K))

include hπ

theorem valuation_lt_one_iff_dvd (r : 𝒪) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal 𝒪)
      (ι r) < 1 ↔ π ∣ r := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change r ∈ IsLocalRing.maximalIdeal 𝒪 ↔ _
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem not_dvd_Δ_of_hasGoodReduction (h : (W.map (algebraMap 𝒪 K)).HasGoodReduction 𝒪) :
    ¬π ∣ W.Δ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_Δ]
  exact h.goodReduction.not_lt

theorem not_dvd_c₄_of_hasMultiplicativeReduction
    (h : (W.map (algebraMap 𝒪 K)).HasMultiplicativeReduction 𝒪) : ¬π ∣ W.c₄ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_c₄]
  exact h.multiplicativeReduction.not_lt

theorem dvd_c₄_of_hasAdditiveReduction
    (h : (W.map (algebraMap 𝒪 K)).HasAdditiveReduction 𝒪) : π ∣ W.c₄ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_c₄]
  exact h.additiveReduction

theorem dvd_Δ_of_hasMultiplicativeReduction
    (h : (W.map (algebraMap 𝒪 K)).HasMultiplicativeReduction 𝒪) : π ∣ W.Δ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_Δ]
  exact h.badReduction

omit hπ in

theorem scale_map_eq (V : WeierstrassCurve 𝒪) (b₁ b₂ b₃ b₄ b₆ : 𝒪) (hπK : ι π ≠ 0)
    (h1 : V.a₁ = π * b₁) (h2 : V.a₂ = π ^ 2 * b₂) (h3 : V.a₃ = π ^ 3 * b₃)
    (h4 : V.a₄ = π ^ 4 * b₄) (h6 : V.a₆ = π ^ 6 * b₆) :
    (⟨Units.mk0 (ι π) hπK, 0, 0, 0⟩ : VariableChange K) • V.map (algebraMap 𝒪 K) =
      (⟨b₁, b₂, b₃, b₄, b₆⟩ : WeierstrassCurve 𝒪).map (algebraMap 𝒪 K) := by
  rw [variableChange_def]
  ext
  · simp only [WeierstrassCurve.map_a₁, h1, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₁, h2, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₁, h3, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₁, h4, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₆, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₁, h6, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] hπ in
theorem Δ_scale (V : WeierstrassCurve 𝒪) (b₁ b₂ b₃ b₄ b₆ : 𝒪)
    (h1 : V.a₁ = π * b₁) (h2 : V.a₂ = π ^ 2 * b₂) (h3 : V.a₃ = π ^ 3 * b₃)
    (h4 : V.a₄ = π ^ 4 * b₄) (h6 : V.a₆ = π ^ 6 * b₆) :
    V.Δ = π ^ 12 * (⟨b₁, b₂, b₃, b₄, b₆⟩ : WeierstrassCurve 𝒪).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h1, h2, h3, h4, h6]
  ring

theorem notScalable_of_isMinimal [h : IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))] (hΔ : W.Δ ≠ 0) :
    ∀ C : VariableChange 𝒪, ¬Scalable π (C • W) := by
  rintro C ⟨⟨b₁, h1⟩, ⟨b₂, h2⟩, ⟨b₃, h3⟩, ⟨b₄, h4⟩, ⟨b₆, h6⟩⟩
  have hπK : ι π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hπ.ne_zero
  have hD := scale_map_eq K (C • W) b₁ b₂ b₃ b₄ b₆ hπK h1 h2 h3 h4 h6
  have hΔ' := Δ_scale (C • W) b₁ b₂ b₃ b₄ b₆ h1 h2 h3 h4 h6
  set W' : WeierstrassCurve 𝒪 := ⟨b₁, b₂, b₃, b₄, b₆⟩
  set D : VariableChange K := ⟨Units.mk0 (ι π) hπK, 0, 0, 0⟩
  have hj : (D * C.map (algebraMap 𝒪 K)) • W.map (algebraMap 𝒪 K) = W'.map (algebraMap 𝒪 K) := by
    rw [mul_smul, map_variableChange, hD]
  have hint : IsIntegral 𝒪 ((D * C.map (algebraMap 𝒪 K)) • W.map (algebraMap 𝒪 K)) := by
    rw [hj]; infer_instance
  have hle := h.val_Δ_maximal.2 hint
  dsimp only at hle
  rw [one_smul, hj] at hle
  have hΔC : (C • W).Δ = ((C.u⁻¹ : 𝒪ˣ) : 𝒪) ^ 12 * W.Δ := variableChange_Δ W C
  set v := IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal 𝒪)
  have hvπ : v (ι π) < 1 := (valuation_lt_one_iff_dvd K hπ π).2 dvd_rfl
  have hW'0 : W'.Δ ≠ 0 := by
    intro h0
    apply hΔ
    have : (C • W).Δ = 0 := by rw [hΔ', h0, mul_zero]
    rw [hΔC] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (Units.ne_zero _))
  have hv0 : 0 < v (ι W'.Δ) := by
    rw [zero_lt_iff, Ne, map_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hW'0
  have key : v (ι W.Δ) = v (ι π) ^ 12 * v (ι W'.Δ) := by
    have e2 : W.Δ = ((C.u : 𝒪ˣ) : 𝒪) ^ 12 * (π ^ 12 * W'.Δ) := by
      rw [← hΔ', hΔC, ← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_pow, one_mul]
    have hvu' : v (ι ((C.u : 𝒪ˣ) : 𝒪)) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun hm => (mem_maximalIdeal _).1 hm (Units.isUnit _)
    rw [e2, map_mul, map_mul, map_pow, map_mul, map_pow, hvu', one_pow, one_mul, map_mul, map_pow,
      map_pow]
  have hlt : v (ι W.Δ) < v (ι W'.Δ) := by
    rw [key]
    exact mul_lt_of_lt_one_left hv0 (pow_lt_one₀ zero_le hvπ (by norm_num))
  have e1 : (valuation_Δ_aux 𝒪 (W.map (algebraMap 𝒪 K)) : WithZero (Multiplicative ℤ)) =
      v (ι W.Δ) := by
    rw [valuation_Δ_aux_eq_of_isIntegral, map_Δ]
  have e2 : (valuation_Δ_aux 𝒪 (W'.map (algebraMap 𝒪 K)) : WithZero (Multiplicative ℤ)) =
      v (ι W'.Δ) := by
    rw [valuation_Δ_aux_eq_of_isIntegral, map_Δ]
  have := hle (by rw [← Subtype.coe_le_coe, e1, e2]; exact hlt.le)
  rw [← Subtype.coe_le_coe, e1, e2] at this
  exact absurd this (not_le.2 hlt)

end Reduction

theorem Δ_ne_zero_of_isElliptic {𝒪 : Type*} [CommRing 𝒪] (K : Type*) [Field K] [Algebra 𝒪 K]
    (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] : W.Δ ≠ 0 := by
  intro h
  have := (W.map (algebraMap 𝒪 K)).isUnit_Δ
  rw [map_Δ, h, map_zero] at this
  exact not_isUnit_zero this

section Types

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)

local notation "ι" => algebraMap 𝒪 K

include hπ

theorem knBound_good (hΔ : ¬π ∣ W.Δ) : KNBound K W 1 := by
  refine knBound_one K W fun P => ?_
  by_contra hP
  obtain ⟨x, y, h, -, hs⟩ := (notMem_E0Set_iff K W P).1 hP
  have he := equation_residue W (equation_of_map K W h.1)
  haveI : (W.map (residue 𝒪)).IsElliptic := by
    rw [isElliptic_iff, map_Δ, isUnit_iff_ne_zero, Ne, ← dvd_iff_residue_eq_zero hπ]
    exact hΔ
  exact hs ((equation_iff_nonsingular (W := W.map (residue 𝒪))).1 he)

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem splitPoly_origin {x₀ y₀ : 𝒪}
    (h3 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₃)
    (h4 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₄)
    (h6 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₆) :
    ((C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X - C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)).map
      (algebraMap 𝒪 (ResidueField 𝒪))) =
      C (residue 𝒪 W.c₄) * (X ^ 2 + C (residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₁) * X
        - C (residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₂)) := by
  set W₁ := (⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W
  have e1 : W₁.a₁ = W.a₁ := by simp [W₁, variableChange_a₁]
  have e2 : W₁.a₂ = W.a₂ + 3 * x₀ := by simp [W₁, variableChange_a₂]
  have eb : 54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄ =
      (54 * W₁.b₆ - 3 * W₁.b₂ * W₁.b₄) + W₁.a₂ * W.c₄ := by
    simp only [W₁, variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_a₂,
      inv_one, Units.val_one, one_pow, one_mul, WeierstrassCurve.c₄]
    ring
  have hb : π ∣ 54 * W₁.b₆ - 3 * W₁.b₂ * W₁.b₄ := by
    have hb4 : π ∣ W₁.b₄ := by
      rw [WeierstrassCurve.b₄]
      exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_mul_of_dvd_right h3 _)
    have hb6 : π ∣ W₁.b₆ := by
      rw [WeierstrassCurve.b₆]
      exact dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_of_dvd_right h6 4)
    exact dvd_sub (dvd_mul_of_dvd_right hb6 54) (dvd_mul_of_dvd_right hb4 _)
  rw [(dvd_iff_residue_eq_zero hπ)] at hb
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_C, map_X, ResidueField.algebraMap_eq]
  rw [eb, map_add, hb, zero_add, ← e1]
  simp only [map_mul]
  ring

theorem knBound_nonsplit [IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))]
    (hm : (W.map (algebraMap 𝒪 K)).HasMultiplicativeReduction 𝒪)
    (hns : ¬(W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪) : KNBound K W 2 := by
  by_cases hall : ∀ P, P ∈ E0Set K W
  · exact (knBound_one K W hall).mono K (by norm_num)
  push Not at hall
  obtain ⟨P, hP⟩ := hall
  obtain ⟨x₀, y₀, h₀, -, hs⟩ := (notMem_E0Set_iff K W P).1 hP
  have e₀ := equation_of_map K W h₀.1
  obtain ⟨h6, h3, h4⟩ := origin_vc W hπ e₀ hs
  refine KNBound.of_vc K W ⟨1, x₀, 0, y₀⟩ ?_
  refine knBound_of_no_tangent K _ hπ h3 h4 (by rw [h6]; exact dvd_zero _) fun s hs' => hns ?_
  refine { toHasMultiplicativeReduction := hm, splitMultiplicativeReduction := ?_ }
  rw [integralModel_map, splitPoly_origin W hπ h3 h4 (by rw [h6]; exact dvd_zero _)]
  set a := residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₁
  have hroot : residue 𝒪 s ^ 2 + a * residue 𝒪 s -
      residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₂ = 0 := by
    have := (dvd_iff_residue_eq_zero hπ).1 hs'
    simpa using this
  have hfac : X ^ 2 + C a * X - C (residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₂) =
      (X - C (residue 𝒪 s)) * (X - C (-residue 𝒪 s - a)) := by
    rw [show residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₂ =
      residue 𝒪 s ^ 2 + a * residue 𝒪 s by linear_combination -hroot]
    simp only [C_add, C_mul, C_pow, C_neg, C_sub]
    ring
  rw [hfac]
  exact (Splits.C _).mul ((Splits.X_sub_C _).mul (Splits.X_sub_C _))

theorem knBound_of_not_split [IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))]
    (hns : ¬(W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪) : KNBound K W 4 := by
  have hΔ := Δ_ne_zero_of_isElliptic K W
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
    (R := 𝒪) (W := W.map (algebraMap 𝒪 K)) with hg | hm | ha
  · exact (knBound_good K W hπ (not_dvd_Δ_of_hasGoodReduction K W hπ hg)).mono K (by norm_num)
  · exact (knBound_nonsplit K W hπ hm hns).mono K (by norm_num)
  · exact knBound_additive K W hπ hΔ (notScalable_of_isMinimal K W hπ hΔ)
      (dvd_c₄_of_hasAdditiveReduction K W hπ ha)

end Types

end

end GroundTheory.Arith.Abelian

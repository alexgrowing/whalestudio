import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronTate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing IsDiscreteValuationRing Polynomial

noncomputable section

section Node

variable {F : Type*} [Field F] (V : WeierstrassCurve F)

theorem exists_node (hΔ : V.Δ = 0) (hc : V.c₄ ≠ 0) :
    ∃ x y : F, V.toAffine.Equation x y ∧
      V.a₁ * y - (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) = 0 ∧ 2 * y + V.a₁ * x + V.a₃ = 0 := by
  by_cases h2 : (2 : F) = 0
  · have ha : V.a₁ ≠ 0 := by
      intro h0
      apply hc
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h0]
      linear_combination (8 * V.a₂ ^ 2 - 24 * V.a₄) * h2
    set x₀ := V.a₃ / V.a₁ with hx₀
    set y₀ := (x₀ ^ 2 + V.a₄) / V.a₁ with hy₀
    refine ⟨x₀, y₀, ?_, ?_, ?_⟩
    · rw [Affine.equation_iff']
      have key : V.a₁ ^ 6 * (y₀ ^ 2 + V.a₁ * x₀ * y₀ + V.a₃ * y₀ -
          (x₀ ^ 3 + V.a₂ * x₀ ^ 2 + V.a₄ * x₀ + V.a₆)) = V.Δ + 2 * (6 * V.a₁ ^ 4 * V.a₂ * V.a₆ -
          4 * V.a₁ ^ 3 * V.a₂ * V.a₃ * V.a₄ - 18 * V.a₁ ^ 3 * V.a₃ * V.a₆ +
          4 * V.a₁ ^ 2 * V.a₂ ^ 2 * V.a₃ ^ 2 + 24 * V.a₁ ^ 2 * V.a₂ ^ 2 * V.a₆ -
          4 * V.a₁ ^ 2 * V.a₂ * V.a₄ ^ 2 + 16 * V.a₁ ^ 2 * V.a₃ ^ 2 * V.a₄ -
          36 * V.a₁ ^ 2 * V.a₄ * V.a₆ - 8 * V.a₁ * V.a₂ ^ 2 * V.a₃ * V.a₄ -
          18 * V.a₁ * V.a₂ * V.a₃ ^ 3 - 72 * V.a₁ * V.a₂ * V.a₃ * V.a₆ +
          48 * V.a₁ * V.a₃ * V.a₄ ^ 2 + 8 * V.a₂ ^ 3 * V.a₃ ^ 2 + 32 * V.a₂ ^ 3 * V.a₆ -
          8 * V.a₂ ^ 2 * V.a₄ ^ 2 - 36 * V.a₂ * V.a₃ ^ 2 * V.a₄ - 144 * V.a₂ * V.a₄ * V.a₆ +
          14 * V.a₃ ^ 4 + 108 * V.a₃ ^ 2 * V.a₆ + 32 * V.a₄ ^ 3 + 216 * V.a₆ ^ 2) := by
        rw [hy₀, hx₀]
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        field_simp
        ring
      rw [hΔ, h2, zero_mul, add_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 6 ha)
    · rw [hy₀]; field_simp; linear_combination (-(x₀ ^ 2) - V.a₂ * x₀) * h2
    · rw [hx₀]; field_simp; linear_combination (y₀ + V.a₃) * h2
  · set x₀ := (18 * V.b₆ - V.b₂ * V.b₄) / V.c₄ with hx₀
    have hD : V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) + 32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 -
        36 * V.b₂ * V.b₄ * V.b₆ = 0 := by
      have := V.b_relation
      rw [WeierstrassCurve.Δ] at hΔ
      linear_combination -4 * hΔ - V.b₂ ^ 2 * this
    have hc4 : V.c₄ = V.b₂ ^ 2 - 24 * V.b₄ := rfl
    have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have hf : 4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆ = 0 := by
      have key : V.c₄ ^ 3 * (4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆) =
          (V.b₂ ^ 3 - 36 * V.b₂ * V.b₄ + 216 * V.b₆) * (V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) +
            32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 - 36 * V.b₂ * V.b₄ * V.b₆) := by
        rw [hx₀]; field_simp; rw [hc4]; ring
      rw [hD, mul_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 3 hc)
    have hf' : 12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄ = 0 := by
      have key : V.c₄ ^ 2 * (12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) =
          36 * (V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) + 32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 -
            36 * V.b₂ * V.b₄ * V.b₆) := by
        rw [hx₀]; field_simp; rw [hc4]; ring
      rw [hD, mul_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hc)
    refine ⟨x₀, -(V.a₁ * x₀ + V.a₃) / 2, ?_, ?_, ?_⟩
    · rw [Affine.equation_iff']
      have : (-(V.a₁ * x₀ + V.a₃) / 2) ^ 2 + V.a₁ * x₀ * (-(V.a₁ * x₀ + V.a₃) / 2) +
          V.a₃ * (-(V.a₁ * x₀ + V.a₃) / 2) - (x₀ ^ 3 + V.a₂ * x₀ ^ 2 + V.a₄ * x₀ + V.a₆) =
          -(4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆) / 4 := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        field_simp; ring
      rw [this, hf]; simp
    · have : V.a₁ * (-(V.a₁ * x₀ + V.a₃) / 2) - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) =
          -(12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) / 4 := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
        field_simp; ring
      rw [this, hf']; simp
    · field_simp; ring

end Node

section Form

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [DecidableEq (ResidueField 𝒪)] {π : 𝒪}
  (hπ : Irreducible π) (W : WeierstrassCurve 𝒪)
include hπ

theorem tate_step2 (V : WeierstrassCurve 𝒪) (h2 : V.a₂ = 0) (he : IsUnit V.a₁) (h3 : π ∣ V.a₃)
    (h4 : π ∣ V.a₄) (h6 : π ∣ V.a₆) :
    ∃ r s t : 𝒪, ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₂ = 0 ∧
      ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₃ = 0 ∧
      ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₄ = 0 ∧
      IsUnit ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₁ ∧
      π ∣ ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₆ := by
  have hγ : IsUnit (12 * V.a₃ - V.a₁ ^ 3) := by
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply (isUnit_iff_not_dvd hπ).1 (he.pow 3)
    have := dvd_sub (dvd_mul_of_dvd_right h3 12) h
    convert this using 1; ring
  obtain ⟨t, dt, ht⟩ := exists_root_cubic hπ (α := 0) (β := 12) hγ
    (δ := 3 * V.a₃ ^ 2 + V.a₁ ^ 2 * V.a₄)
    (dvd_add (dvd_mul_of_dvd_right (dvd_pow h3 two_ne_zero) 3) (dvd_mul_of_dvd_right h4 _))
  obtain ⟨r, hr⟩ : ∃ r, V.a₁ * r = -(V.a₃ + 2 * t) := ⟨-(V.a₃ + 2 * t) * ↑he.unit⁻¹, by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩
  have dr : π ∣ r := by
    have h1 : π ∣ V.a₁ * r := by rw [hr]; exact dvd_neg.2 (dvd_add h3 (dvd_mul_of_dvd_right dt 2))
    exact (he.dvd_mul_left).1 h1
  obtain ⟨s, ds, hs⟩ := exists_root_cubic hπ (α := 0) (β := 1) he (δ := -(3 * r))
    (dvd_neg.2 (dvd_mul_of_dvd_right dr 3))
  refine ⟨r, s, t, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul, h2]
    linear_combination -hs
  · simp only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hr
  · simp only [variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, h2]
    have hk : V.a₁ ^ 2 * (V.a₄ - t * V.a₁ + 3 * r ^ 2 - s * (V.a₁ * r + V.a₃ + 2 * t)) = 0 := by
      linear_combination ht + (3 * (V.a₁ * r - V.a₃ - 2 * t) - V.a₁ ^ 2 * s) * hr
    have hk' := (mul_eq_zero.1 hk).resolve_left (pow_ne_zero 2 he.ne_zero)
    linear_combination hk'
  · simp only [variableChange_a₁, inv_one, Units.val_one, one_mul]
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply (isUnit_iff_not_dvd hπ).1 he
    have := dvd_sub h (dvd_mul_of_dvd_right ds 2)
    rwa [add_sub_cancel_right] at this
  · simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, h2]
    exact dvd_sub (dvd_sub (dvd_sub (dvd_add (dvd_add (dvd_add h6 (dvd_mul_of_dvd_left dr _))
      (dvd_mul_of_dvd_left (dvd_pow dr two_ne_zero) _)) (dvd_pow dr three_ne_zero))
      (dvd_mul_of_dvd_left dt _)) (dvd_pow dt two_ne_zero)) (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left dr _) _)

theorem tate_step1 (W : WeierstrassCurve 𝒪) (hc : ¬π ∣ W.c₄) (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄)
    (h6 : π ∣ W.a₆) {s₀ : 𝒪} (hs₀ : π ∣ s₀ ^ 2 + W.a₁ * s₀ - W.a₂) :
    ∃ s₁ : 𝒪, ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₂ = 0 ∧
      IsUnit ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₁ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₃ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₄ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₆ := by
  have hb4 : π ∣ W.b₄ := by
    rw [WeierstrassCurve.b₄]; exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_mul_of_dvd_right h3 _)
  have hb2 : ¬π ∣ W.b₂ := fun h => hc (by
    rw [WeierstrassCurve.c₄]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right hb4 24))
  have hγ₁ : IsUnit (2 * s₀ + W.a₁) := by
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply hb2
    have : W.b₂ = (2 * s₀ + W.a₁) ^ 2 - 4 * (s₀ ^ 2 + W.a₁ * s₀ - W.a₂) := by
      rw [WeierstrassCurve.b₂]; ring
    rw [this]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right hs₀ 4)
  obtain ⟨Z, -, hZ⟩ := exists_root_cubic hπ (α := 0) (β := 1) hγ₁ hs₀
  have hs₁ : (s₀ + Z) ^ 2 + W.a₁ * (s₀ + Z) - W.a₂ = 0 := by linear_combination hZ
  refine ⟨s₀ + Z, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -hs₁
  · simp only [variableChange_a₁, inv_one, Units.val_one, one_mul]
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply hb2
    have : W.b₂ = (W.a₁ + 2 * (s₀ + Z)) ^ 2 - 4 * ((s₀ + Z) ^ 2 + W.a₁ * (s₀ + Z) - W.a₂) := by
      rw [WeierstrassCurve.b₂]; ring
    rw [this, hs₁, mul_zero, sub_zero]
    exact dvd_pow h two_ne_zero
  · simp only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero]
    exact h3
  · simp only [variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero, sub_zero, zero_pow two_ne_zero]
    exact dvd_sub h4 (dvd_mul_of_dvd_right h3 _)
  · simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero, sub_zero, zero_pow two_ne_zero, zero_pow three_ne_zero]
    exact h6

end Form

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K
local notation "v" => addVal 𝒪

theorem split_equiv [IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))]
    (hs : (W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪) :
    Nonempty ((curveK K W).Point ⧸ E0 K W ≃+ ZMod (v W.Δ).toNat) := by
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪
  have hm := hs.toHasMultiplicativeReduction
  have hc := not_dvd_c₄_of_hasMultiplicativeReduction K W hπ hm
  have hΔ := dvd_Δ_of_hasMultiplicativeReduction K W hπ hm
  have hres : ∀ {a : 𝒪}, π ∣ a ↔ residue 𝒪 a = 0 := dvd_iff_residue_eq_zero hπ
  obtain ⟨xb, yb, heb, hAb, hBb⟩ := exists_node (W.map (residue 𝒪))
    (by rw [map_Δ]; exact hres.1 hΔ) (by rw [map_c₄]; exact fun h => hc (hres.2 h))
  obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective xb
  obtain ⟨y₀, rfl⟩ := IsLocalRing.residue_surjective yb
  rw [Affine.equation_iff'] at heb
  set C₀ : VariableChange 𝒪 := ⟨1, x₀, 0, y₀⟩ with hC₀
  have h3 : π ∣ (C₀ • W).a₃ := by
    rw [hres]
    simp only [hC₀, variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_ofNat]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hBb
    linear_combination hBb
  have h4 : π ∣ (C₀ • W).a₄ := by
    rw [hres]
    simp only [hC₀, variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_sub, map_pow, map_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄] at hAb
    linear_combination -hAb
  have h6 : π ∣ (C₀ • W).a₆ := by
    rw [hres]
    simp only [hC₀, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_sub, map_pow]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heb
    linear_combination -heb
  have hc₀ : ¬π ∣ (C₀ • W).c₄ := by
    rw [variableChange_c₄]; simpa [hC₀] using hc

  have hsp := hs.splitMultiplicativeReduction
  rw [integralModel_map, splitPoly_origin W hπ h3 h4 h6] at hsp
  have hc4r : residue 𝒪 W.c₄ ≠ 0 := fun h => hc (hres.2 h)
  have hdeg : (C (residue 𝒪 W.c₄) * (X ^ 2 + C (residue 𝒪 (C₀ • W).a₁) * X -
      C (residue 𝒪 (C₀ • W).a₂))).degree ≠ 0 := by
    rw [degree_C_mul hc4r, show (X ^ 2 + C (residue 𝒪 (C₀ • W).a₁) * X -
      C (residue 𝒪 (C₀ • W).a₂) : Polynomial (ResidueField 𝒪)) = C 1 * X ^ 2 +
      C (residue 𝒪 (C₀ • W).a₁) * X + C (-residue 𝒪 (C₀ • W).a₂) by simp [sub_eq_add_neg],
      degree_quadratic one_ne_zero]
    decide
  obtain ⟨sb, hsb⟩ := hsp.exists_eval_eq_zero hdeg
  obtain ⟨s₀, rfl⟩ := IsLocalRing.residue_surjective sb
  have hs₀ : π ∣ s₀ ^ 2 + (C₀ • W).a₁ * s₀ - (C₀ • W).a₂ := by
    rw [hres]
    simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_X] at hsb
    have := (mul_eq_zero.1 hsb).resolve_left hc4r
    simp only [map_sub, map_add, map_mul, map_pow]
    exact this
  obtain ⟨s₁, t2, te, t3, t4, t6⟩ := tate_step1 hπ (C₀ • W) hc₀ h3 h4 h6 hs₀
  obtain ⟨r, s, t, g2, g3, g4, ge, g6⟩ := tate_step2 hπ _ t2 te t3 t4 t6
  set W₂ := (⟨1, r, s, t⟩ : VariableChange 𝒪) • ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • (C₀ • W))
  have eT := tateQuotientEquiv K hπ g2 g3 g4 ge g6
  have hΔ₂ : W₂.Δ = W.Δ := by simp only [W₂, hC₀, vc_Δ_one]
  have hq0 : W₂.a₆ ≠ 0 := a₆_ne_zero K g2 g3 g4
  have hv : v W₂.a₆ = v W.Δ := by
    rw [← hΔ₂]
    have : W₂.Δ = W₂.a₆ * -(W₂.a₁ ^ 6 + 432 * W₂.a₆) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, g2, g3, g4]
      ring
    have hu : IsUnit (-(W₂.a₁ ^ 6 + 432 * W₂.a₆)) := by
      rw [IsUnit.neg_iff, isUnit_iff_not_dvd hπ]
      intro h
      apply (isUnit_iff_not_dvd hπ).1 (ge.pow 6)
      have := dvd_sub h (dvd_mul_of_dvd_right g6 432)
      rwa [add_sub_cancel_right] at this
    rw [this, addVal_mul, v_unit hu, add_zero]
  exact ⟨(quotientE0VariableChangeEquiv K W C₀).trans ((quotientE0VariableChangeEquiv K (C₀ • W) ⟨1, 0, s₁, 0⟩).trans
    ((quotientE0VariableChangeEquiv K _ ⟨1, r, s, t⟩).trans
      (eT.trans (ZMod.ringEquivCongr (by rw [hv])).toAddEquiv)))⟩

theorem kodaira_neron [IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))] :
    Finite ((curveK K W).Point ⧸ E0 K W) ∧
    (¬(W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪 →
      Nat.card ((curveK K W).Point ⧸ E0 K W) ≤ 4) ∧
    ((W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪 →
      IsAddCyclic ((curveK K W).Point ⧸ E0 K W) ∧
        (Nat.card ((curveK K W).Point ⧸ E0 K W) : ℕ∞) = v W.Δ) := by
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪
  by_cases hs : (W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪
  · obtain ⟨e⟩ := split_equiv K W hs
    have hΔ0 : W.Δ ≠ 0 := Δ_ne_zero_of_isElliptic K W
    have hn : v W.Δ ≠ ⊤ := v_ne_top hΔ0
    have hn1 : 1 ≤ (v W.Δ).toNat := by
      have h1 := (one_le_v_iff hπ).2 (dvd_Δ_of_hasMultiplicativeReduction K W hπ
        hs.toHasMultiplicativeReduction)
      lift v W.Δ to ℕ using hn with m hm
      simp only [ENat.toNat_natCast]
      exact_mod_cast h1
    have : NeZero (v W.Δ).toNat := ⟨by omega⟩
    refine ⟨Finite.of_equiv _ e.toEquiv.symm, fun h => absurd hs h, fun _ => ⟨?_, ?_⟩⟩
    · exact isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective
    · rw [Nat.card_congr e.toEquiv, Nat.card_zmod, ENat.natCast_toNat hn]
  · have hb := knBound_of_not_split K W hπ hs
    exact ⟨hb.1, fun _ => hb.2, fun h => absurd h hs⟩

end Main

end

end GroundTheory.Arith.Abelian

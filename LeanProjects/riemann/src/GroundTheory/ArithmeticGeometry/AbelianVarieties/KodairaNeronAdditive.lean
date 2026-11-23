import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronIstar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

noncomputable section

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] hπ in

theorem notScalable_vc {W : WeierstrassCurve 𝒪} (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    (C : VariableChange 𝒪) : ∀ C' : VariableChange 𝒪, ¬Scalable π (C' • C • W) := by
  intro C'
  rw [← mul_smul]
  exact hmin _

theorem knBound_of_no_tangent (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ∣ W.a₆)
    (hno : ∀ s : 𝒪, ¬π ∣ s ^ 2 + W.a₁ * s - W.a₂) : KNBound K W 2 := by
  refine knBound_two K W fun P Q R hP hQ hR hs => ?_
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, -, -, -, -, -, -, dx₁, -, dx₂, -, dx₃, -, -, -, -, v1, -,
    -⟩ := triple_origin K W hπ h3 h4 h6 hP hQ hR hs
  apply hno ℓ
  rw [← v1]
  exact dvd_add (dvd_add dx₁ dx₂) dx₃

theorem kodairaNeron_bound_of_pi_cube_a6 (hΔ : W.Δ ≠ 0) (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    {A₁ A₂ A₃ A₄ A₆ : 𝒪} (h1 : W.a₁ = π * A₁) (h2 : W.a₂ = π * A₂)
    (h3 : W.a₃ = π ^ 2 * A₃) (h4 : W.a₄ = π ^ 2 * A₄) (h6 : W.a₆ = π ^ 3 * A₆) :
    KNBound K W 4 := by
  by_cases hex : ∃ x y X : 𝒪, W.toAffine.Equation x y ∧ x = π * X ∧ π ∣ y ∧
      π ∣ 3 * X ^ 2 + 2 * A₂ * X + A₄
  · obtain ⟨x, y, X, e, rfl, dy, hD⟩ := hex
    have hP := (pi_sq_dvd_y_of_double_root W hπ h1 h2 h3 h4 h6 e rfl dy).2
    obtain ⟨s1, s2, s3, s4, s6⟩ := variableChange_raises_divisibility W hπ h1 h2 h3 h4 h6 hP hD
    refine KNBound.of_vc K W ⟨1, π * X, 0, 0⟩ ?_
    have hmin' := notScalable_vc hmin ⟨1, π * X, 0, 0⟩
    obtain ⟨B₃, hB₃⟩ := s3
    obtain ⟨B₆', hB₆'⟩ := s6
    by_cases hA : π ^ 2 ∣ ((⟨1, π * X, 0, 0⟩ : VariableChange 𝒪) • W).a₂
    · refine (knBound_star K _ hπ s1 hA hB₃ s4 hB₆' ?_).mono K (by norm_num)
      intro C'
      exact hmin' C'
    · obtain ⟨A₂', hA₂'⟩ := s2
      have hA₂'' : ¬π ∣ A₂' := by
        rintro ⟨c, rfl⟩; exact hA ⟨c, by rw [hA₂']; ring⟩
      exact knBound_Istar K _ hπ (by rwa [vc_Δ_one]) ⟨s1, ⟨A₂', hA₂', hA₂''⟩, ⟨B₃, hB₃⟩, s4,
        ⟨B₆', hB₆'⟩⟩
  · push Not at hex
    exact knBound_I0star K W hπ h1 h2 h3 h4 h6 fun x y X e hx hy hD => hex x y X e hx hy hD

theorem kodairaNeron_bound_of_pi_sq_dvd_a6 (hΔ : W.Δ ≠ 0) (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ^ 2 ∣ W.a₆) :
    KNBound K W 4 := by
  have d6 : π ∣ W.a₆ := (dvd_pow_self π two_ne_zero).trans h6
  by_cases h4' : π ^ 2 ∣ W.a₄
  · obtain ⟨A₃, hA₃⟩ := h3
    obtain ⟨A₆, hA₆⟩ := h6
    by_cases hex : ∃ x y Y : 𝒪, W.toAffine.Equation x y ∧ π ∣ x ∧ y = π * Y ∧ π ∣ 2 * Y + A₃
    · obtain ⟨x, y, Y, e, dx, hy, hD⟩ := hex
      obtain ⟨s1, s2, s3, s4, s6⟩ := vc_IV_step W hπ h1 h2 hA₃ h4' hA₆ e dx hy hD
      refine KNBound.of_vc K W ⟨1, 0, 0, y⟩ ?_
      obtain ⟨B₁, hB₁⟩ := s1
      obtain ⟨B₂, hB₂⟩ := s2
      obtain ⟨B₃, hB₃⟩ := s3
      obtain ⟨B₄, hB₄⟩ := s4
      obtain ⟨B₆, hB₆⟩ := s6
      exact kodairaNeron_bound_of_pi_cube_a6 K _ hπ (by rwa [vc_Δ_one]) (notScalable_vc hmin _) hB₁ hB₂ hB₃ hB₄ hB₆
    · push Not at hex
      exact (knBound_IV K W hπ h1 h2 hA₃ h4' hA₆ fun x y Y e dx hy hD =>
        hex x y Y e dx hy hD).mono K (by norm_num)
  · exact (knBound_III K W hπ h1 h2 h3 h4 d6 h4').mono K (by norm_num)

theorem knBound_cusp_origin (hΔ : W.Δ ≠ 0) (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ^ 2 ∣ W.a₆) (hb₂ : π ∣ W.b₂) : KNBound K W 4 := by
  have d6 : π ∣ W.a₆ := (dvd_pow_self π two_ne_zero).trans h6
  by_cases hex : ∃ s : 𝒪, π ∣ s ^ 2 + W.a₁ * s - W.a₂
  · obtain ⟨s, hs⟩ := hex
    refine KNBound.of_vc K W ⟨1, 0, s, 0⟩ ?_
    have e1 : ((⟨1, 0, s, 0⟩ : VariableChange 𝒪) • W).a₁ = W.a₁ + 2 * s := by
      simp [variableChange_a₁]
    have e2 : ((⟨1, 0, s, 0⟩ : VariableChange 𝒪) • W).a₂ = -(s ^ 2 + W.a₁ * s - W.a₂) := by
      simp [variableChange_a₂]; ring
    have e3 : ((⟨1, 0, s, 0⟩ : VariableChange 𝒪) • W).a₃ = W.a₃ := by
      simp [variableChange_a₃]
    have e4 : ((⟨1, 0, s, 0⟩ : VariableChange 𝒪) • W).a₄ = W.a₄ - s * W.a₃ := by
      simp [variableChange_a₄]
    have e6 : ((⟨1, 0, s, 0⟩ : VariableChange 𝒪) • W).a₆ = W.a₆ := by
      simp [variableChange_a₆]
    have d1 : π ∣ W.a₁ + 2 * s := by
      apply hπ.prime.dvd_of_dvd_pow (n := 2)
      have : (W.a₁ + 2 * s) ^ 2 = W.b₂ + 4 * (s ^ 2 + W.a₁ * s - W.a₂) := by
        rw [WeierstrassCurve.b₂]; ring
      rw [this]
      exact dvd_add hb₂ (dvd_mul_of_dvd_right hs 4)
    refine kodairaNeron_bound_of_pi_sq_dvd_a6 K _ hπ (by rwa [vc_Δ_one]) (notScalable_vc hmin _) (by rw [e1]; exact d1)
      (by rw [e2]; exact hs.neg_right) (by rw [e3]; exact h3)
      (by rw [e4]; exact dvd_sub h4 (dvd_mul_of_dvd_right h3 s)) (by rw [e6]; exact h6)
  · push Not at hex
    exact (knBound_of_no_tangent K W hπ h3 h4 d6 hex).mono K (by norm_num)

theorem knBound_additive (hΔ : W.Δ ≠ 0) (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    (hc₄ : π ∣ W.c₄) : KNBound K W 4 := by
  by_cases hall : ∀ P, P ∈ E0Set K W
  · exact (knBound_one K W hall).mono K (by norm_num)
  push Not at hall
  obtain ⟨P, hP⟩ := hall
  obtain ⟨x₀, y₀, h₀, -, hs⟩ := (notMem_E0Set_iff K W P).1 hP
  have e₀ := equation_of_map K W h₀.1
  obtain ⟨h6, h3, h4⟩ := origin_vc W hπ e₀ hs
  refine KNBound.of_vc K W ⟨1, x₀, 0, y₀⟩ ?_
  refine knBound_cusp_origin K _ hπ (by rwa [vc_Δ_one]) (notScalable_vc hmin _) h3 h4
    (by rw [h6]; exact dvd_zero _) ?_
  have hc : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).c₄ := by
    rw [variableChange_c₄]; simpa using hc₄
  apply hπ.prime.dvd_of_dvd_pow (n := 2)
  have hb4 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).b₄ := by
    rw [WeierstrassCurve.b₄]
    exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_mul_of_dvd_right h3 _)
  have : ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).b₂ ^ 2 =
      ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).c₄ +
        24 * ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).b₄ := by
    rw [WeierstrassCurve.c₄]; ring
  rw [this]
  exact dvd_add hc (dvd_mul_of_dvd_right hb4 24)

end Bound

end

end GroundTheory.Arith.Abelian

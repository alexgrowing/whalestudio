import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimate
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapIntegrabilityStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.FamilyDerivativeExpansion.BeL

theorem eq_zero_of_rankOne {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {a : W}
    (h : (innerSL ℂ a).smulRight a = 0) : a = 0 := by
  have h1 := congrArg (fun T : W →L[ℂ] W => T a) h
  simpa using h1

theorem exists_normalised_bessel_map : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -⟩ := id hside
  obtain ⟨L, hL⟩ := hH.1.2.2.2 k r ε mu R Wp z u₀ π μW μN hDS hz hT hπ hW hN
  have hTK : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.T.discreteSeries_unitary_smooth_basic hH.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
  by_cases h0 : ∀ v ∈ R.TK, L v = 0
  · refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2, h0 v hv]
    ext ξ
    simp
  · push Not at h0
    obtain ⟨v₀, hv₀, hne⟩ := h0
    have hB := Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul
      (GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside v₀ hv₀ (L v₀)) (⟪L v₀, L v₀⟫_ℂ)⁻¹
    have e : ∀ w ∈ R.sm, (⟪L v₀, L v₀⟫_ℂ)⁻¹ • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ (L v₀) = L w := by
      intro w hw
      rw [(hL w hw v₀ (hTK _ hv₀)).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
        inv_mul_cancel₀ (inner_self_ne_zero.2 hne), one_smul]
    refine ⟨_, hB, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2]
    simp only [e w hw, e v (hTK v hv)]

theorem isBeL_of_normalised_on_orbitSpan : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (w₀ : R.H) (l : R.H → Wp), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → PI.UpqRep.IsLowUnitH k r ε mu R.σ w₀ → IsBes R z π l → (∀ x ∈ DDsp R.σ w₀, ∀ y ∈ DDsp R.σ w₀, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x)) → IsBeL R z π μW μN l := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq w₀ l hds hgap hok hside hlow hB hDD
  obtain ⟨l₀, hB₀, h₀⟩ := exists_normalised_bessel_map hH k r ε mu h R Wp z π u μW μN μG νq hds hgap hok hside
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  have hCyc : PI.SmoothCyc := hH.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKF k r ε mu R hds).2.2.2.2.1
  have hwK : R.KFin w₀ := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hle : ∀ x ∈ DDsp R.σ w₀, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w₀, hwK, rfl⟩
  have hnz := Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w₀ Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
  have hcmp : ∀ x ∈ DDsp R.σ w₀, ∀ y ∈ DDsp R.σ w₀,
      (innerSL ℂ (l y)).smulRight (l x) = (innerSL ℂ (l₀ y)).smulRight (l₀ x) :=
    fun x hx y hy => (hDD x hx y hy).symm.trans (h₀ x (hsm x (hle x hx)) y (hle y hy)).2
  refine ⟨hB, fun w hw v hv => ⟨(h₀ w hw v hv).1, ?_⟩⟩
  rw [(h₀ w hw v hv).2]
  by_cases hz : ∀ x ∈ DDsp R.σ w₀, l x = 0
  · have hl : ∀ x ∈ DDsp R.σ w₀, l₀ x = 0 := by
      intro x hx
      apply eq_zero_of_rankOne
      rw [← hcmp x hx x hx, hz x hx]
      simp
    rw [hnz l₀ hB₀ hl w hw, hnz l hB hz w hw]
    simp
  · push Not at hz
    obtain ⟨y, hy, hy0⟩ := hz
    have hyy : ⟪l y, l y⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hy0
    set c : ℂ := (⟪l y, l y⟫_ℂ)⁻¹ * ⟪l₀ y, l y⟫_ℂ with hc
    have h1 : ∀ x ∈ DDsp R.σ w₀, l x = c • l₀ x := by
      intro x hx
      have := congrArg (fun T : Wp →L[ℂ] Wp => T (l y)) (hcmp x hx y hy)
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at this
      rw [hc, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hyy, one_smul]
    have h2 : ∀ x ∈ R.sm, l x = c • l₀ x := by
      intro x hx
      have := hnz _ (Kap.bessel_add hB (Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hB₀ (-c)))
        (fun x hx => by rw [h1 x hx, neg_smul, add_neg_cancel]) x hx
      simpa only [neg_smul, add_neg_eq_zero] using this
    have h3 : starRingEnd ℂ c * c = 1 := by
      have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l₀ y)) (hcmp y hy y hy)
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at h4
      have hl0 : l₀ y ≠ 0 := fun e => hy0 (by rw [h1 y hy, e, smul_zero])
      rw [h1 y hy, inner_smul_left, smul_smul] at h4
      have h5 := smul_left_injective ℂ hl0 h4
      have h6 : ⟪l₀ y, l₀ y⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hl0
      apply mul_right_cancel₀ h6
      linear_combination h5
    rw [h2 w hw, h2 v (hsm v hv)]
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, smul_smul]
    congr 1
    linear_combination (-⟪l₀ v, ξ⟫_ℂ) * h3

end CompanionTheory.FamilyDerivativeExpansion.BeL

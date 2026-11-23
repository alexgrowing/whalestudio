import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.JQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaQExpansionIntegral
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries GroundTheory.Global.Elliptic Function
open scoped MatrixGroups Manifold

noncomputable section

namespace JQExpansion

lemma periodic_comp_ofComplex_of {f : ℍ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → f (ofComplex (z + 1)) = f (ofComplex z)) :
    Periodic (f ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  intro w
  simp only [comp_apply, Complex.ofReal_one]
  by_cases hw : 0 < w.im
  · exact hf w hw
  · have hw' : (w + 1).im ≤ 0 := by simpa using hw
    rw [ofComplex_apply_eq_of_im_nonpos hw' (not_lt.mp hw)]

theorem proof : JQExpansion.Statement := by
  set Q : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ with hQdef
  set φ : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ * modularJ τ with hφdef
  have hqper : ∀ z : ℂ, Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := fun z ↦ by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
  have hQper : Periodic (Q ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [hQdef, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1,
]
      exact hqper z
  have hφper : Periodic (φ ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hE := SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL z
      have hD := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL z
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [comp_apply, Complex.ofReal_one, CuspForm.coe_discriminant] at hE hD
      simp only [hφdef, modularJ, hE, hD]
      rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
      simp only [hqper]
  have hQhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q := UpperHalfPlane.mdifferentiable_iff.mpr
    ((Periodic.differentiable_qParam (h := 1)).differentiableOn.congr fun z hz ↦ by
      simp [hQdef, ofComplex_apply_of_im_pos (show 0 < z.im from hz)])
  have hφhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ := UpperHalfPlane.mdifferentiable_iff.mpr
    ((UpperHalfPlane.mdifferentiable_iff.mp hQhol).mul differentiableOn_modularJC)
  have hQb : IsBoundedAtImInfty Q :=
    isBoundedAtImInfty_iff.mpr ⟨1, 0, fun τ _ ↦ (Periodic.norm_qParam_lt_one one_pos τ.im_pos).le⟩
  have hφb : IsBoundedAtImInfty φ := by
    obtain ⟨M, A, hM⟩ := isBoundedAtImInfty_iff.mp (ModularFormClass.bdd_at_infty E₄)
    obtain ⟨C, hC⟩ := exp_isBigO_discriminant.bound
    obtain ⟨A', hA'⟩ := (atImInfty_mem _).mp hC
    refine isBoundedAtImInfty_iff.mpr ⟨C * M ^ 3, max A A', fun τ hτ ↦ ?_⟩
    have h1 := hM τ (le_of_max_le_left hτ)
    have hΔ : 0 < ‖ModularForm.discriminant τ‖ := norm_pos_iff.mpr (discriminant_ne_zero τ)
    have h2 : ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ ≤ C := by
      have h3 := hA' τ (le_of_max_le_right hτ)
      simp only [Set.mem_ofPred_eq, Real.norm_of_nonneg (Real.exp_pos _).le] at h3
      rw [div_le_iff₀ hΔ, Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
      exact h3
    calc ‖φ τ‖ = ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ 3 := by
          simp only [hφdef, modularJ, norm_mul, norm_div, norm_pow]
          ring
      _ ≤ C * M ^ 3 := mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 3) (by positivity)
          (le_trans (by positivity) h2)
  have hQa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hQper hQhol hQb
  have hφa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hφper hφhol hφb
  have hΔa := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  have hE3a := ModularFormClass.analyticAt_cuspFunction_zero (E₄.pow 3) one_pos
    one_mem_strictPeriods_SL

  have hQX : qExpansion 1 Q = X := by
    have hsum : ∀ τ : ℍ, HasSum
        (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) (Q τ) := by
      intro τ
      have e : (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) =
          fun n ↦ if n = 1 then Periodic.qParam 1 (τ : ℂ) else 0 := by
        funext n
        split_ifs with h <;> simp [h]
      rw [e]
      exact hasSum_ite_eq 1 _
    ext m
    have h := UpperHalfPlane.qExpansion_coeff_unique (⟨Q, hQhol.continuous⟩ : C(ℍ, ℂ)) one_pos
      hQa hsum m
    rw [coeff_X]
    exact h.symm

  have hprod : φ * ⇑CuspForm.discriminant = Q * ⇑(E₄.pow 3) := by
    funext τ
    have := discriminant_ne_zero τ
    simp only [Pi.mul_apply, hφdef, hQdef, modularJ, ModularForm.coe_pow, Pi.pow_apply,
      CuspForm.coe_discriminant]
    field_simp
  have hq := congrArg (qExpansion 1) hprod
  obtain ⟨D, hD0, hΔ⟩ := DeltaQExpansionIntegral.proof
  rw [UpperHalfPlane.qExpansion_mul hφa hΔa, UpperHalfPlane.qExpansion_mul hQa hE3a, hQX,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    DeltaQExpansionIntegral.qExpansion_E₄, CuspForm.coe_discriminant, hΔ, map_mul, map_X,
    ← mul_assoc, mul_comm (qExpansion 1 φ) X, mul_assoc] at hq
  have hq' := mul_left_cancel₀ X_ne_zero hq
  set E4Z : PowerSeries ℤ := 1 + (240 : ℤ) • DeltaQExpansionIntegral.sigmaSeries 3 with hE4Z
  set u := invOfUnit D 1 with hu
  have hDu : D * u = 1 := mul_invOfUnit D 1 (by simp [hD0])
  have ha : qExpansion 1 φ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
    calc qExpansion 1 φ = qExpansion 1 φ * map (Int.castRingHom ℂ) (D * u) := by
          rw [hDu, map_one, mul_one]
      _ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
          rw [map_mul, ← mul_assoc, hq', map_mul, map_pow]
  refine ⟨fun n ↦ coeff n (E4Z ^ 3 * u), ?_, fun τ ↦ ?_⟩
  · simp [hu, hE4Z, constantCoeff_invOfUnit, DeltaQExpansionIntegral.sigmaSeries]
  · have h := UpperHalfPlane.hasSum_qExpansion one_pos hφper hφhol hφb τ
    have e : ∀ n, coeff n (map (Int.castRingHom ℂ) (E4Z ^ 3 * u)) = ((coeff n (E4Z ^ 3 * u) : ℤ) : ℂ) :=
      fun n ↦ by rw [coeff_map, eq_intCast]
    simp only [ha, e, smul_eq_mul] at h
    exact h

end JQExpansion

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.approx :
    UpperTheory.V.Cj.H.Approx := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F hF
  by_contra hF0
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hcont := GlobalTheory.AutomorphicL2Unitary.continuous_R (Γ := Γ) (μ := μ) F
  obtain ⟨f, hfc, hfs, hfr, hf1, hfW, hfF⟩ :=
    hF {g | ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2} (by
      apply (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const))
        continuous_const).mem_nhds
      show ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ 1 F - F‖ < ‖F‖ / 2
      rw [map_one, ContinuousLinearMap.one_apply, sub_self, norm_zero]
      positivity)
  have hfre : ∀ y, f y = ((f y).re : ℂ) := by
    intro y
    obtain ⟨t, _, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
  have hfnn : ∀ y, 0 ≤ (f y).re := by
    intro y
    obtain ⟨t, ht0, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
    exact ht0
  have hint : MeasureTheory.Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hrep := (GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hint) F
  have hφ := hrep.1
  have hzero : ∫ g, f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F ∂μ = 0 := hrep.2.symm.trans hfF
  have hI : ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ = 0 := by
    rw [integral_re (hφ.const_inner F), integral_inner hφ F, hzero, inner_zero_right]
    simp
  have hbound : ∀ g, ‖F‖ ^ 2 / 2 * (f g).re
      ≤ RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) := by
    intro g
    have hre : RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F))
        = (f g).re * (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
      rw [inner_smul_right]
      conv_lhs => rw [hfre g]
      simp
    rw [hre]
    by_cases hg : ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2
    · have e1 : inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
          = inner ℂ F F - inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) := by
        rw [inner_sub_right]
        ring
      have e2 : (inner ℂ F F).re = ‖F‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
      have e3 := re_inner_le_norm (𝕜 := ℂ) F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
      rw [norm_sub_rev] at e3
      have e4 : ‖F‖ ^ 2 / 2 ≤ (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
        rw [e1, Complex.sub_re, e2]
        have e3' : (inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re ≤ ‖F‖ * (‖F‖ / 2) := by
          simp only [RCLike.re_to_complex] at e3
          exact e3.trans (mul_le_mul_of_nonneg_left hg.le (norm_nonneg F))
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left e4 (hfnn g)
      linarith
    · have h0 : f g = 0 := hfW g hg
      rw [h0]
      simp
  have hpos2 : 0 < ∫ g, (f g).re ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hfc) (hfs.comp_left Complex.zero_re) (fun y => hfnn y)
      (by
        intro h
        apply hf1
        rw [hfre 1, h, Complex.ofReal_zero])
  have hmono : ∫ g, ‖F‖ ^ 2 / 2 * (f g).re ∂μ
      ≤ ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ :=
    MeasureTheory.integral_mono (hint.re.const_mul _) ((hφ.const_inner F).re) hbound
  rw [hI, MeasureTheory.integral_const_mul] at hmono
  have h6 : 0 < ‖F‖ ^ 2 / 2 * ∫ g, (f g).re ∂μ := mul_pos (by positivity) hpos2
  linarith

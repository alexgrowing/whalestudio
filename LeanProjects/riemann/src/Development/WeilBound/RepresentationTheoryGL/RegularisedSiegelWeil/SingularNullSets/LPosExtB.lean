import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtA
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X]

theorem est {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {G h : X → ℂ}
    (hG : Integrable G μ) (hh : Integrable h μ) {C : ℝ} (hoff : ∀ x ∉ K, G x - h x = 0)
    (hon : ∀ x ∈ K, ‖G x - h x‖ ≤ C) : ‖∫ x, G x ∂μ - ∫ x, h x ∂μ‖ ≤ C * μ.real K := by
  rw [← integral_sub hG hh, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx => hoff x hx)]
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hon

variable [BorelSpace X]

theorem uniq (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (ν ν' : Measure X) [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts ν']
    (heq : ∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') (g : C_c(X, ℝ)) : ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
  obtain ⟨b, hbA, -, hb1⟩ := hbump (tsupport g) g.hasCompactSupport
  obtain ⟨B, hB⟩ := (hA b hbA).1.bounded_above_of_compact_support (hA b hbA).2
  have hK : IsCompact (tsupport b) := (hA b hbA).2
  have hbK : ∀ x ∉ tsupport b, b x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  let G : X → ℂ := fun x => (g x : ℂ)
  have hG : Continuous G := Complex.continuous_ofReal.comp g.continuous
  have hGc : HasCompactSupport G := g.hasCompactSupport.comp_left Complex.ofReal_zero
  have hGb : ∀ x, G x ≠ 0 → b x = 1 := fun x hx =>
    hb1 x (subset_tsupport _ (by simpa [G, Function.mem_support] using hx))
  have hGK : ∀ x ∉ tsupport b, G x = 0 := by
    intro x hx
    by_contra h0
    have := hGb x h0
    rw [hbK x hx] at this
    exact zero_ne_one this
  have key : ∫ x, G x ∂ν - ∫ x, G x ∂ν' = 0 := by
    apply zero_of_le _ (B * (ν.real (tsupport b) + ν'.real (tsupport b)))
    intro ε hε
    obtain ⟨h, hhA, hh⟩ := approx A (fun f hf => (hA f hf).1) hmul hstar hsep hK hbA hbK hG hGb hε
    have hoff : ∀ x ∉ tsupport b, G x - h x = 0 := by
      intro x hx
      have := hh x
      rw [hbK x hx, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at this
      rw [this, sub_self]
    have hon : ∀ x ∈ tsupport b, ‖G x - h x‖ ≤ ε * B := by
      intro x _
      rw [norm_sub_rev]
      exact (hh x).trans (mul_le_mul_of_nonneg_left (hB x) hε.le)
    have hGi : ∀ μ : Measure X, IsFiniteMeasureOnCompacts μ → Integrable G μ :=
      fun μ _ => hG.integrable_of_hasCompactSupport hGc
    have hhi : ∀ μ : Measure X, IsFiniteMeasureOnCompacts μ → Integrable h μ :=
      fun μ _ => (hA h hhA).1.integrable_of_hasCompactSupport (hA h hhA).2
    have e1 := est hK (hGi ν inferInstance) (hhi ν inferInstance) hoff hon
    have e2 := est hK (hGi ν' inferInstance) (hhi ν' inferInstance) hoff hon
    have : ∫ x, G x ∂ν - ∫ x, G x ∂ν' = (∫ x, G x ∂ν - ∫ x, h x ∂ν) - (∫ x, G x ∂ν' - ∫ x, h x ∂ν') := by
      rw [heq h hhA]; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [e1, e2]
  have h2 : ((∫ x, g x ∂ν : ℝ) : ℂ) = ((∫ x, g x ∂ν' : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact sub_eq_zero.mp key
  exact_mod_cast h2

theorem uniq' [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (ν ν' : Measure X) (hν : IsFiniteMeasureOnCompacts ν) (hν' : IsFiniteMeasureOnCompacts ν')
    (heq : ∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') : ν = ν' :=
  Measure.ext_of_integral_eq_on_compactlySupported (uniq A hA hmul hstar hsep hbump ν ν' heq)

end PositivityTheory.Rg.Rsw.L.LPosExt

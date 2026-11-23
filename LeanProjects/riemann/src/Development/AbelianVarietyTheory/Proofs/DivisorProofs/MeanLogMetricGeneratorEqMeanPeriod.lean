import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralCoeIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MeanPeriodGenerator

theorem ellT_eq_span (D : D7) (cD : D.what₂.Tau → ℂ) (h : IsDgen D cD)
    (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M)
    (τ : D.what₂.Tau) (hc : cD τ ∈ M) :
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {(⟨cD τ, hc⟩ : M)} := by
  obtain ⟨M₀, _, hM₀, hs⟩ := h
  obtain ⟨s, hsc, hs⟩ := hs τ
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm
  have hc0 : cD τ ≠ 0 := fun h => hs0 (Subtype.ext (hsc.trans h))
  haveI : NumberField (M ⊔ M₀ : IntermediateField ℚ ℂ) := NumberField.mk
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ (M ⊔ M₀ : IntermediateField ℚ ℂ) :=
    fun τ x => (le_sup_left : M ≤ M ⊔ M₀) (hM τ x)
  have h' := GlobalTheory.EigenlineBaseChange.ellT_eq_span_of_le D M₀ (M ⊔ M₀) le_sup_right hM₀ τ s hs
  apply le_antisymm
  · intro x hx
    have hx' : (⟨(x : ℂ), (le_sup_left : M ≤ M ⊔ M₀) x.2⟩ : (M ⊔ M₀ : IntermediateField ℚ ℂ)) ∈
        TaylorLogMetric.ellT D (M ⊔ M₀) τ := by
      rw [GlobalTheory.Glob.mem_ellT_iff hM']
      exact (GlobalTheory.Glob.mem_ellT_iff hM τ x).1 hx
    rw [h', Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hcx⟩ := hx'
    have e : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) * (s : ℂ) = (x : ℂ) :=
      congrArg (fun a : (M ⊔ M₀ : IntermediateField ℚ ℂ) => (a : ℂ)) hcx
    have hi : IsIntegral ℤ ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) :=
      (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).2 c.isIntegral_coe
    have e2 : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) = (x : ℂ) * (cD τ)⁻¹ := by
      rw [← e, hsc, mul_inv_cancel_right₀ hc0]
    rw [e2] at hi
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨cD τ, hc⟩ : M)⁻¹, (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).1 hi⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hc0 (congrArg (fun a : M => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM]
    have := (GlobalTheory.Glob.mem_ellT_iff hM₀ τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)
    rw [hsc] at this
    exact this

theorem mean_logMet_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  intro D cc dl cD hc hmean hgen
  have hne : ∀ τ, cD τ ≠ 0 := by
    intro τ h
    obtain ⟨M₀, _, hM₀, hs⟩ := hgen
    obtain ⟨s, hsc, hs⟩ := hs τ
    exact GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm (Subtype.ext (hsc.trans h))
  refine ⟨hne, fun M _ hD hcM τ => ?_⟩
  haveI : NumberField M := NumberField.mk
  have hell := ellT_eq_span D cD hgen M hD.1 τ (hcM τ)
  have hl : TaylorLogMetric.liftM M (cD τ) = ⟨cD τ, hcM τ⟩ := dif_pos (hcM τ)
  rw [hl, ← hmean M hD τ, Finset.sum_neg_distrib]
  exact (GlobalTheory.Glob.meanLogOm_eq_of_gen hD.1 (GlobalTheory.Glob.area_lamConj_pos hc hD) hell.symm).symm

end GlobalTheory.MeanPeriodGenerator

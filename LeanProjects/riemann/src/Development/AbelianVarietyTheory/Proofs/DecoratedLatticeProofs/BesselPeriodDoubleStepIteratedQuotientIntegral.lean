import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quotient_integral_finset_sum_eq {ι : Type} (s : Finset ι) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext x
    rw [Finset.sum_insert ha]
    rfl

theorem quotient_integral_finset_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, a i * F i x) (∑ i ∈ s, a i * Z i) :=
  quotient_integral_finset_sum_eq s (fun i x => a i * F i x) (fun i => a i * Z i) fun i hi => (hF i hi).smul (a i)

end Quot

end GlobalTheory.SeeSaw.Assemble

end

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble

set_option maxHeartbeats 4000000 in

theorem doubleStep_tuple : ∀ (D : D7) (c : Comm D) (t : Tup c), DoubleStep D → c.Is → t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ), (∀ a, IsContAut (c.X j) (φ a)) → RapidDec _ f → RapidDec _ (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) → ∃ F₁ : GA D (c.V (j + 1)) → ℂ, IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ F₁ (t.perF j (σ + 1) h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) ∧ ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (t.integrand j σ h P₁ P₂ φ f h₁) (F₁ h₁) := by
  intro D c t hDS hc ht j σ h P₁ P₂ φ f hφ hf hrap
  obtain ⟨hom₁, hvW₁⟩ := ht.sBF j (σ + 1) h
  obtain ⟨hom₂, hvW₂⟩ := ht.sFB j σ h
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hΦ₁ := ht.pt j hj1 P₁
  have hΦ₂ := ht.pt (j + 1) hj2 P₂

  have hstep : ∀ α, ∀ g : GA D (c.V j), ∃ f₁ : GA D (c.V (j + 1)) → ℂ,
      IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ f₁
        ((c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁)))) ∧
      ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ
        (fun h₂ => (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂)
          (rTrans h₂ f)) (f₁ h₁) := by
    intro α g
    have hr : RapidDec _ ((t.sFB j σ h).lift f (t.pt (j + 1) P₂)) := by
      unfold Step.lift; rw [hom₂, hvW₂]; exact hrap
    obtain ⟨-, f₁, h1, h2⟩ := hDS c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) f g
      hΦ₁ hΦ₂ (hφ α) hf hr
    refine ⟨f₁, ?_, fun h₁ => ?_⟩
    · have h1' := h1
      unfold Step.lift at h1'
      rw [hom₁, hvW₁, hom₂, hvW₂] at h1'
      exact h1'
    · have h2' := h2 h₁
      rw [hvW₂] at h2'
      exact h2'
  choose f₁ hf₁ using hstep

  have hw := (t.sBF j (σ + 1) h).weil
  rw [hom₁] at hw
  have hcont := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D c.ψ (c.V j) (c.V (j + 1)) _ _ (t.om j) hw (c.vol (j + 1))
    (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁) hrap hΦ₁).2.2.1
  refine ⟨fun h₁ => ∑ α, ∑ g ∈ (t.e j α).support, t.e j α g * f₁ α g h₁, ?_, fun h₁ => ?_⟩
  · have hper : ∀ α, (c.B j (σ + 1) h).per c.ψ (φ α) (trc (t.e j α) (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) =
        ∑ g ∈ (t.e j α).support, t.e j α g * (c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ
          (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂))
          (t.pt j P₁))) := fun α =>
      ((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std (σ + 1) (c.B j (σ + 1) h) (φ α) (hφ α)).2 (t.e j α) _ hcont).2
    unfold Tup.perF
    simp only [hper]
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).1
  · unfold Tup.integrand
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).2 h₁

end GlobalTheory.SeeSaw.Assemble

end

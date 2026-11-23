import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

variable {e n : ℕ}

theorem continuous_comp_emb (σ : Fin n ↪ Fin e) :
    Continuous (fun w : Fin e → ℂ => w ∘ σ) :=
  continuous_pi fun j => continuous_apply (σ j)

theorem analyticAt_comp_emb (σ : Fin n ↪ Fin e) (w : Fin e → ℂ) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => v ∘ σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (σ j)).analyticAt w

theorem extend_comp_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ g w ∘ σ = g :=
  funext fun j => σ.injective.extend_apply g w j

theorem extend_extend_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ (w ∘ σ) (Function.extend σ g w) = w := by
  funext i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    exact σ.injective.extend_apply _ _ j
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

theorem analyticAt_extend_emb (σ : Fin n ↪ Fin e) {f : (Fin n → ℂ) → Fin n → ℂ} {w : Fin e → ℂ}
    (hf : AnalyticAt ℂ f (w ∘ σ)) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v) w := by
  rw [analyticAt_pi_iff]
  intro i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v (σ j)) =
        (fun y : Fin n → ℂ => f y j) ∘ (fun v : Fin e → ℂ => v ∘ σ) := by
      funext v
      exact σ.injective.extend_apply _ _ j
    rw [hfun]
    exact AnalyticAt.comp (analyticAt_pi_iff.1 hf j) (analyticAt_comp_emb σ w)
  · have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v i) = fun v => v i := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt w

noncomputable def extendHomeo (σ : Fin n ↪ Fin e)
    (τ : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h₁ : AnalyticOnNhd ℂ τ τ.source) (h₂ : AnalyticOnNhd ℂ τ.symm τ.target) :
    OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) where
  toFun w := Function.extend σ (τ (w ∘ σ)) w
  invFun w := Function.extend σ (τ.symm (w ∘ σ)) w
  source := {w | w ∘ σ ∈ τ.source}
  target := {w | w ∘ σ ∈ τ.target}
  map_source' w hw := by
    show Function.extend σ (τ (w ∘ σ)) w ∘ σ ∈ τ.target
    rw [extend_comp_emb]
    exact τ.map_source hw
  map_target' w hw := by
    show Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ ∈ τ.source
    rw [extend_comp_emb]
    exact τ.map_target hw
  left_inv' w hw := by
    show Function.extend σ (τ.symm (Function.extend σ (τ (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.left_inv hw, extend_extend_emb]
  right_inv' w hw := by
    show Function.extend σ (τ (Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ.symm (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.right_inv hw, extend_extend_emb]
  open_source := τ.open_source.preimage (continuous_comp_emb σ)
  open_target := τ.open_target.preimage (continuous_comp_emb σ)
  continuousOn_toFun := fun w hw =>
    (analyticAt_extend_emb σ (h₁ _ hw)).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw =>
    (analyticAt_extend_emb σ (h₂ _ hw)).continuousAt.continuousWithinAt

theorem chart_swap :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

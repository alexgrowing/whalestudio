import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace KTypeIsomorphism

variable {ι : Type*} {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem inner_lc (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f f' : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ y₂ f) (Finsupp.linearCombination ℂ y₂ f') =
      inner ℂ (Finsupp.linearCombination ℂ y₁ f) (Finsupp.linearCombination ℂ y₁ f') := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hI]

theorem norm_lc (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ y₂ f‖ = ‖Finsupp.linearCombination ℂ y₁ f‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_lc y₁ y₂ hI]

theorem lc_mem (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) (f : ι →₀ ℂ) :
    Finsupp.linearCombination ℂ y₁ f ∈ C₁ := by
  have h : Finsupp.linearCombination ℂ y₁ f ∈ Submodule.span ℂ (Set.range y₁) := by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ f
  exact Submodule.span_le.2 (Set.range_subset_iff.2 h₁) h

def lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) : (ι →₀ ℂ) →ₗ[ℂ] C₁ :=
  (Finsupp.linearCombination ℂ y₁).codRestrict C₁ (lc_mem y₁ C₁ h₁)

theorem dense_lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure) : DenseRange (lcC y₁ C₁ h₁) := by
  intro x
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  show (x : H₁) ∈ closure (Subtype.val '' Set.range (lcC y₁ C₁ h₁))
  have he : Subtype.val '' Set.range (lcC y₁ C₁ h₁) = (Submodule.span ℂ (Set.range y₁) : Set H₁) := by
    rw [← Set.range_comp, ← Finsupp.range_linearCombination, LinearMap.coe_range]
    rfl
  rw [he, ← Submodule.topologicalClosure_coe]
  exact hd₁ x.2

variable [CompleteSpace H₁] [CompleteSpace H₂]

theorem gns_extend (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j))
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (hC₁ : IsClosed (C₁ : Set H₁)) (hC₂ : IsClosed (C₂ : Set H₂))
    (h₁ : ∀ i, y₁ i ∈ C₁) (h₂ : ∀ i, y₂ i ∈ C₂)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (hd₂ : C₂ ≤ (Submodule.span ℂ (Set.range y₂)).topologicalClosure) :
    ∃ U : C₁ ≃ₗᵢ[ℂ] C₂, ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f := by
  have : CompleteSpace C₁ := hC₁.completeSpace_coe
  have : CompleteSpace C₂ := hC₂.completeSpace_coe
  have hn : ∀ f, ‖lcC y₂ C₂ h₂ ((LinearEquiv.refl ℂ (ι →₀ ℂ)) f)‖ = ‖lcC y₁ C₁ h₁ f‖ := by
    intro f
    show ‖(lcC y₂ C₂ h₂ f : H₂)‖ = ‖(lcC y₁ C₁ h₁ f : H₁)‖
    exact norm_lc y₁ y₂ hI f
  refine ⟨(LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry (lcC y₁ C₁ h₁) (lcC y₂ C₂ h₂)
    (dense_lcC y₁ C₁ h₁ hd₁) (dense_lcC y₂ C₂ h₂ hd₂) hn, ?_⟩
  intro f x hx
  have hx' : x = lcC y₁ C₁ h₁ f := Subtype.ext hx
  subst hx'
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

theorem gns_intertwine (y₁ : ι → H₁) (y₂ : ι → H₂)
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (U : C₁ ≃ₗᵢ[ℂ] C₂) (hU : ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f)
    (T₁ : H₁ →L[ℂ] H₁) (T₂ : H₂ →L[ℂ] H₂) (τ : ι → ι) (hT₁ : ∀ i, T₁ (y₁ i) = y₁ (τ i))
    (hT₂ : ∀ i, T₂ (y₂ i) = y₂ (τ i)) (hTC : ∀ x ∈ C₁, T₁ x ∈ C₁) :
    ∀ x y : C₁, (x : H₁) = T₁ (y : H₁) → ((U x : C₂) : H₂) = T₂ ((U y : C₂) : H₂) := by
  let R : C₁ →L[ℂ] C₁ := (T₁.comp C₁.subtypeL).codRestrict C₁ (fun y => hTC _ y.2)
  let A : C₁ →L[ℂ] H₂ := C₂.subtypeL.comp (U.toLinearIsometry.toContinuousLinearMap.comp R)
  let B : C₁ →L[ℂ] H₂ := T₂.comp (C₂.subtypeL.comp U.toLinearIsometry.toContinuousLinearMap)
  have hAB : (A : C₁ → H₂) = B := by
    refine (dense_lcC y₁ C₁ h₁ hd₁).equalizer A.continuous B.continuous (funext fun f => ?_)
    show ((U (R (lcC y₁ C₁ h₁ f)) : C₂) : H₂) = T₂ ((U (lcC y₁ C₁ h₁ f) : C₂) : H₂)
    have hR : ((R (lcC y₁ C₁ h₁ f) : C₁) : H₁) =
        Finsupp.linearCombination ℂ y₁ (Finsupp.mapDomain τ f) := by
      show T₁ (Finsupp.linearCombination ℂ y₁ f) = _
      rw [Finsupp.linearCombination_mapDomain]
      have := Finsupp.apply_linearCombination ℂ T₁.toLinearMap y₁ f
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, show (⇑T₁ ∘ y₁) = y₁ ∘ τ from funext hT₁]
    rw [hU _ _ hR, hU f _ rfl, Finsupp.linearCombination_mapDomain]
    have := Finsupp.apply_linearCombination ℂ T₂.toLinearMap y₂ f
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, show (⇑T₂ ∘ y₂) = y₂ ∘ τ from funext hT₂]
  intro x y hxy
  have hx : x = R y := Subtype.ext hxy
  subst hx
  exact congrFun hAB y

end KTypeIsomorphism

end ReciprocityTheory.ChartRestriction.DS

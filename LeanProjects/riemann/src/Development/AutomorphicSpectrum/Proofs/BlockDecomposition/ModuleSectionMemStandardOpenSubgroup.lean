import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem moduleSection_mem_standardOpenSubgroup {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (t : {r : ℝ // 0 < r}) :
    moduleSection w t ∈ standardOpenSubgroup F := by
  have h1 : ∀ s : {r : ℝ // 0 < r}, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((moduleSection w s : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro s v
    rw [← coe_finiteProj]
    simp [moduleSection, finiteProj_infiniteEmbedding]
  rw [mem_standardOpenSubgroup]
  intro v
  refine ⟨?_, ?_⟩
  · rw [h1]; exact one_mem _
  · rw [← map_inv, h1]; exact one_mem _

theorem differentiableOn_continuedLFunction :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker →
        DifferentiableOn ℂ χ.continuedLFunction {1}ᶜ := by
  intro F _ _ χ hU
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      (χ.toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    let w : InfinitePlace F := Classical.arbitrary _
    have hs : ∀ t : {x : ℝ // 0 < x}, χ.toIdele (moduleSection w t) = 1 := fun t ↦
      MonoidHom.mem_ker.1 (hU (moduleSection_mem_standardOpenSubgroup w t))
    have h0 : archExponent w χ = 0 := archExponent_unique w χ fun t ↦ by simp [hs t]
    have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
    have hd := HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ
    simpa [hτ0] using hd
  · exact (χ.differentiable_continuedLFunction h).differentiableOn

end GlobalTheory.CompanionTheory.PartialZeta

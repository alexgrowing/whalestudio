import Mathlib
import GroundTheory.GlobalFields.TateThesis.TateMain

open NumberField Topology Filter Complex Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem eqOn_of_differentiableOn_of_eq_globalZeta {F : 𝔸[K] → ℂ} {χ : HeckeCharacter K}
    {S : Set ℂ} (hS : S.Finite) (hSre : ∀ z ∈ S, z.re ≤ 1) {G H : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G Sᶜ) (hH : DifferentiableOn ℂ H Sᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s)
    (hHZ : ∀ s : ℂ, 1 < s.re → H s = globalZeta F χ s) : EqOn G H Sᶜ := by
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hU : IsPreconnected Sᶜ :=
    (hS.countable.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have h2 : (2 : ℂ) ∈ Sᶜ := fun h ↦ by
    have := hSre 2 h
    norm_num at this
  have heq : G =ᶠ[𝓝 (2 : ℂ)] H :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun s hs ↦ (hGZ s hs).trans (hHZ s hs).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hopen)
    (hH.analyticOnNhd hopen) hU h2 heq

theorem eq_tateZeta_of_differentiable {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {χ : HeckeCharacter K} (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    G = tateZeta F χ := by
  have h := eqOn_of_differentiableOn_of_eq_globalZeta (S := ∅) finite_empty (by simp)
    hG.differentiableOn (differentiable_tateZeta hF hχ).differentiableOn hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  funext s
  exact h (by simp)

theorem eqOn_tateZeta_of_differentiableOn {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    EqOn G (tateZeta F χ) {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ := by
  refine eqOn_of_differentiableOn_of_eq_globalZeta (toFinite _) ?_ hG ?_ hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  · intro z hz
    rcases hz with rfl | rfl <;> simp
  · intro s hs
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact (differentiableAt_tateZeta hτ hF hs.1 hs.2).differentiableWithinAt

end

end GroundTheory.Global

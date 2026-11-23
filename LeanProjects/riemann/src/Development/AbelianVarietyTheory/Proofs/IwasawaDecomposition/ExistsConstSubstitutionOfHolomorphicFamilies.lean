import Mathlib
open Filter Topology

namespace GlobalTheory

theorem countable_eq_of_differentiableOn_of_ne {g : ℕ} {U : Set ℂ} {f f' : ℂ → Fin g → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hf' : DifferentiableOn ℂ f' U) (hne : ¬ Set.EqOn f f' U) :
    {w | w ∈ U ∧ f w = f' w}.Countable := by
  set T := {w | w ∈ U ∧ f w = f' w} with hT
  have key : ∀ x ∈ T, ({x} : Set ℂ) ∈ 𝓝[T] x := by
    intro x hx
    have h1 : ¬ ∃ᶠ z in 𝓝[≠] x, f z = f' z := fun h =>
      hne ((hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
        (hf'.analyticOnNhd hU) hc hx.1 h)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at h1
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [h1] with z hz hzT
    by_contra hzx
    exact hz hzx hzT.2
  obtain ⟨t, -, ht, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin key
  refine ht.mono fun x hx => ?_
  have := hcov hx
  simpa using this

theorem exists_const_substitution_of_holomorphic_families :
    ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  intro L D _ g act U s s' hU hc hne hs hs' h
  by_contra hcon
  push_neg at hcon
  choose w hw a ha using hcon
  have hcount : ∀ δ, {z | z ∈ U ∧ s' z (a δ) = s z (act δ (a δ))}.Countable := fun δ =>
    countable_eq_of_differentiableOn_of_ne hU hc (hs' (a δ)) (hs (act δ (a δ)))
      (fun hE => ha δ (hE (hw δ)))
  have hUc : U.Countable := by
    refine (Set.countable_iUnion hcount).mono fun z hz => ?_
    obtain ⟨δ, hδ⟩ := h z hz
    exact Set.mem_iUnion.2 ⟨δ, hz, hδ _⟩
  have hd : Dense Uᶜ := hUc.dense_compl ℝ
  obtain ⟨x, hx1, hx2⟩ := hd.inter_open_nonempty U hU hne
  exact hx2 hx1

end GlobalTheory

import Mathlib
open scoped ContDiff Topology
open Filter

namespace GlobalTheory

theorem smooth_local_exp_glue : ∀ {e : ℕ} (N c : (Fin e → ℂ) → ℝ) (B : Set (Fin e → ℂ)), IsOpen B → Dense {z | c z ≠ 0} → (∀ z0 ∈ B, ∃ V : Set (Fin e → ℂ), IsOpen V ∧ z0 ∈ V ∧ ∃ F : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ F V ∧ ∀ z ∈ V ∩ B, N z = c z * Real.exp (-F z)) → ∃ f : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ f B ∧ ∀ z ∈ B, N z = c z * Real.exp (-f z) := by
  intro e N c B hB hS hloc
  classical
  choose! V hVo hzV F hF hNF using hloc
  have key : ∀ a ∈ B, ∀ b ∈ B, ∀ z ∈ V a ∩ V b ∩ B, F a z = F b z := by
    intro a ha b hb
    have hU : IsOpen (V a ∩ V b ∩ B) := ((hVo a ha).inter (hVo b hb)).inter hB
    refine Set.EqOn.of_subset_closure (s := (V a ∩ V b ∩ B) ∩ {z | c z ≠ 0}) ?_
      ((hF a ha).continuousOn.mono (fun y hy => hy.1.1))
      ((hF b hb).continuousOn.mono (fun y hy => hy.1.2))
      Set.inter_subset_left (hS.open_subset_closure_inter hU)
    intro w hw
    have h1 := hNF a ha w ⟨hw.1.1.1, hw.1.2⟩
    have h2 := hNF b hb w ⟨hw.1.1.2, hw.1.2⟩
    have hc : c w ≠ 0 := hw.2
    have : Real.exp (-F a w) = Real.exp (-F b w) := by
      have := h1.symm.trans h2
      exact mul_left_cancel₀ hc this
    have := Real.exp_injective this
    linarith
  refine ⟨fun z => F z z, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn ?_
    intro x hx
    refine ⟨V x, hVo x hx, hzV x hx, ?_⟩
    refine ((hF x hx).mono Set.inter_subset_right).congr ?_
    intro y hy
    exact key y hy.1 x hx y ⟨⟨hzV y hy.1, hy.2⟩, hy.1⟩
  · intro z hz
    exact hNF z hz z ⟨hzV z hz, hz⟩

end GlobalTheory

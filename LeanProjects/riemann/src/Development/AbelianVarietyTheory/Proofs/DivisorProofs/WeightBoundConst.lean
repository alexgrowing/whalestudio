import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianInterpolation

open GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.InterpCurv

def WeightBound {ι : Type} [Fintype ι] (K Cμ : ℝ) (U : Set (ι → ℂ)) (r s : (ι → ℂ) → ℝ)
    (G : (ι → ℂ) → Matrix ι ι ℂ) : Prop :=
  ∀ z ∈ U, 0 ≤ s z ∧ s z ≤ 1 ∧ ∀ ξ : ι → ℂ,
    (del (fun x => (s x : ℂ)) z ξ = 0 ∧ (leviForm s z ξ ξ).re = 0) ∨
    (s z < 1 ∧
      ‖del (fun x => (s x : ℂ)) z ξ‖ ≤ K * (1 - s z) * gnorm (G z) ξ ∧
      ‖del (fun x => (s x : ℂ)) z ξ‖ ^ 2 ≤
        K * gnorm (G z) ξ ^ 2 * s z * (s z + r z ^ (-Cμ) * (1 - s z)) ∧
      |(leviForm s z ξ ξ).re| ≤ K * gnorm (G z) ξ ^ 2 * (s z + r z ^ (-Cμ) * (1 - s z)) ∧
      |(leviForm s z ξ ξ).re| ≤ K * gnorm (G z) ξ ^ 2 * (1 - s z))

theorem weightBound_const {ι : Type} [Fintype ι] (K Cμ : ℝ) (U : Set (ι → ℂ))
    (r : (ι → ℂ) → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    WeightBound K Cμ U r (fun _ => c) G := by
  intro z _
  refine ⟨hc.1, hc.2, fun ξ => Or.inl ⟨?_, ?_⟩⟩
  · simp [del, linPart_apply]
  · have h : (dbar fun _ : ι → ℂ => ((c : ℝ) : ℂ)) = fun _ => 0 := by
      funext x; ext v; simp [dbar, antilinPart_apply]
    simp only [leviForm, ddbar, h]
    simp [del, linPart_apply]

end GlobalTheory.InterpCurv

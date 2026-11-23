import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.ContDiffMulRight

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by
  have hw' : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x w) := hw
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (σ g w))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hFeq⟩ := hw' (g₀ * g) (mul_mem_UH (a := g₀) hg₀ hg)
  refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g),
    hU.preimage (contDiff_mulRight g).continuous, hmem, ?_, ?_⟩
  · exact hF.comp (contDiff_mulRight g).contDiffOn (fun x hx => hx)
  · intro x hx hxI
    have e : σ (x * g) w = F (x * g) := hFeq (x * g) hx (mul_mem_UH hxI hg)
    show σ x (σ g w) = F (x * g)
    rw [← e, hmul.2 x hxI g hg, ContinuousLinearMap.comp_apply]

theorem smooth_sub {v v' : H} (hv : v ∈ smoothVecs Hm σ) (hv' : v' ∈ smoothVecs Hm σ) :
    v - v' ∈ smoothVecs Hm σ := by
  have h₁ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v) := hv
  have h₂ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v') := hv'
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (v - v'))
  intro g₀ hg₀
  obtain ⟨U₁, F₁, hU₁, m₁, hF₁, e₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, m₂, hF₂, e₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun x => F₁ x - F₂ x, hU₁.inter hU₂, ⟨m₁, m₂⟩, ?_, ?_⟩
  · exact (hF₁.mono Set.inter_subset_left).sub (hF₂.mono Set.inter_subset_right)
  · intro x hx hxI
    have a₁ : σ x v = F₁ x := e₁ x hx.1 hxI
    have a₂ : σ x v' = F₂ x := e₂ x hx.2 hxI
    show σ x (v - v') = F₁ x - F₂ x
    rw [map_sub, a₁, a₂]

end PI.PhMeasCore.UnitaryGroupMassFormula

end

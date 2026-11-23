import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarChartSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsChartVel (M : CxModel P d) (e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)) (z w : (Σ k, ι k) → ℂ)
    (v : Fin d → ℂ) : Prop :=
  ∃ γ : ℂ → (Σ k, ι k) → ℂ, γ 0 = z ∧ HasDerivAt γ w 0 ∧
    (∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ γ s ∧ γ s ∈ mcPts P) ∧
    HasDerivAt (fun s => e (M.proj (γ s))) v 0

namespace Line

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

def discL (s : ℂ) : (Σ _ : Unit, Fin 2) → ℂ := fun p => if p.2 = 0 then 1 else s

def velL : (Σ _ : Unit, Fin 2) → ℂ := fun p => if p.2 = 0 then 0 else 1

theorem discL_mem (s : ℂ) : discL s ∈ mcPts (mCoordIdeal yLine) :=
  mem_mcPts_line.2 ⟨0, by simp [discL]⟩

theorem sChart_projL_discL (s : ℂ) : sChart 0 (projL (discL s)) = fun _ => (2 : ℂ)⁻¹ * s := by
  have hne : vecL (discL s) ≠ 0 := vecL_ne_zero (discL_mem s)
  rw [sChart_apply]
  unfold projL
  rw [dif_pos hne, CP.chartCoord_mk]
  funext j
  simp [vecL, discL]

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree

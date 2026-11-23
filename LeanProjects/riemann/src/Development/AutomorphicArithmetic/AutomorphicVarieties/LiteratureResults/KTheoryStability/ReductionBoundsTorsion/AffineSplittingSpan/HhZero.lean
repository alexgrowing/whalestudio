import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.RowExact

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

theorem ru_eq (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : Ru u F = Tc (s u) (Rt (s u)⁻¹ F) := by
  funext x y
  unfold PInv at hF
  have h := hF (s u)⁻¹ (fun i => x i * u) y
  simp only [map_inv, hs] at h
  show F (fun i => x i * u) y = F x (fun j => (s u)⁻¹ * y j * s u * (s u)⁻¹)
  rw [← h]
  congr 1
  · funext i
    rw [hu (x i), inv_mul_cancel_left]
  · funext j
    group

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end

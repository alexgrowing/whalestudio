import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def CoverMass2.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.encard {x | x ∈ M ∧ z x = w} = δ

def CoverMass2.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass2.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

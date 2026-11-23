import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueChartModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod gradedH gradedSys cechC cechZ)

noncomputable section

open RigSymForm

def ResidueChartTransport.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a b r : ℕ) (x : Fin (r + 1) → P.Fn) (𝓜 : ResidueChartModel P a b x) (c₀ : ℤ),
    (∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH ℂ r 𝓜.M 𝓜.G i c)) →
    ∀ c : ℕ, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula

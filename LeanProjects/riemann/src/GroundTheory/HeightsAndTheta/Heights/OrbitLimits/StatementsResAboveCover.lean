import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushResFibreGerms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Topology Filter ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ResAboveCover.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) →
    ∀ (y : Fin n → ℂ), ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      ∀ V' : R.X → Set R.X, (∀ x ∈ resAbove R Ψ y (segre z), V' x ∈ 𝓝 x) →
        ∃ N ∈ 𝓝 z, ∀ v ∈ mcPts P ∩ N, ∃ x ∈ resAbove R Ψ y (segre z), ∃ y₁ ∈ V' x ∩ R.U x,
          SameOrbit v (R.lift x y₁)

end GroundTheory.Heights₂.Heights.Targets

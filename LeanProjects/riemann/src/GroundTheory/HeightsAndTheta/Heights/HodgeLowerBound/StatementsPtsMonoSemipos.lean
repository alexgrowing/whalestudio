import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def PtsMonoSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : HermLine ι) (r : ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ) (N : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → IsSemipositiveH P L → 0 < r → IsPtsNull P e N →
    (∀ z ∈ mcPts P, z ∉ N → g₁ z ≤ g₂ z) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂ →
    ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ ≤
      ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree

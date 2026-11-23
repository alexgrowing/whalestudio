import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def linPullMetric {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ)
    (hN : ∀ u : J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) : ConeMetric ℂ J where
  ρ u := (fsMetric κ).ρ (fun i => ∑ j, (N i j : ℂ) * u j)
  pos u hu := (fsMetric κ).pos _ fun h => hu (hN u h)
  smul c u := by
    have : (fun i => ∑ j, (N i j : ℂ) * (c • u) j) = c • fun i => ∑ j, (N i j : ℂ) * u j := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, (fsMetric κ).smul]

def BlockImageMetrics.Statement : Prop :=
  (∀ (κ J : Type) [Fintype κ] [Fintype J] (N : Matrix κ (Ix J) ℤ)
      (hN : ∀ u : Ix J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) (P : Ideal (MRing (GlobalTheory J))),
      IsSemipositiveRel ⊥ P (HermLine.ofCone (linPullMetric N hN))) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K) (P : Ideal (MRing ι)),
      IsSemipositiveRel ⊥ P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (unitDeg k₀))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

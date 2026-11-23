import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt

namespace ReciprocityTheory.AnForm.P

open MeasureTheory Metric
open scoped ContDiff

noncomputable section

def polyMaxOff {D : ℕ} (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ ReciprocityTheory.AnForm.A.coordDiv S))

def PolyMaxOscStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ),
    (∀ i ∈ S, 1 ≤ m i) →
    ContinuousOn u (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) →
    ReciprocityTheory.AnForm.A.IsPsh (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) u →
    (∀ z ∈ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S,
      -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) →
    ∀ C₁ : ℝ, 1 ≤ C₁ → ∃ C t₀ : ℝ, 0 < t₀ ∧ t₀ < 1 ∧ ∀ t, 0 < t → t ≤ t₀ →
      ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
        -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z (t / (4 * C₁)) ∧
        polyMaxOff S u z (C₁ * t) - polyMaxOff S u z (t / (4 * C₁)) ≤ epsT C t

def RegChartStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ),
    (∀ i ∈ S, 1 ≤ m i) →
    ContDiffOn ℝ ∞ q (ball 0 2) →
    ContDiffOn ℝ ∞ ph (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) →
    ReciprocityTheory.AnForm.A.IsLeviPsh (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) →
    (∀ z ∈ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S,
      -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) →
    (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) →
    ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 0 < t₀ ∧ t₀ < 1 ∧
      (∀ t, 0 < t → t ≤ t₀ →
        ContDiffOn ℝ ∞ (phT t) (ball 0 (5 / 4)) ∧
        ReciprocityTheory.AnForm.A.IsLeviPsh (ball 0 (5 / 4)) (fun z => q z + phT t z) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S,
          ph z ≤ phT t z ∧ phT t z ≤ ph z + t ^ ((1 : ℝ) / 3) + epsT C t * rLoc S m z ∧
          (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧
            q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧
        ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          phT t z ≤ phT t' z + C * epsT C t') ∧
      ∀ K ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K →
        TendstoUniformlyOn phT ph (nhdsWithin 0 (Set.Ioi 0)) K ∧
        TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ ph) (nhdsWithin 0 (Set.Ioi 0)) K ∧
        TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ ph))
          (nhdsWithin 0 (Set.Ioi 0)) K

end

end ReciprocityTheory.AnForm.P

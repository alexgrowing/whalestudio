import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoSeriesThreeStep
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

namespace DeltaTermLin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_add (F G : RP Ψ N) : degFl (F + G) = degFl F + degFl G := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

theorem degFl_zero : degFl (0 : RP Ψ N) = 0 := by
  simp [degFl]

theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem degFl_sum {ι : Type} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degFl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]

end DeltaTermLin

theorem log_mul_degFl_bracket_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (φ : Equiv.Perm (Ψ ⊕ Ψ)) (τ : Ψ) (Q : RP Ψ N), Real.log p * degFl (bracket j φ p k τ * Q) = deltaTerm j p τ (fun n => (φ ^ (n + 1)) (Sum.inl τ)) k Q := by
  intro Ψ _ _ N j p k hp hk φ τ Q
  have hlie : ∀ σ : Ψ ⊕ Ψ, liePs (N := N) j (k - 1) σ = pLie j (k - 1) σ := by
    rintro (s | s) <;> rfl
  have hco := co_series_three_step.1 (Ψ ⊕ Ψ) φ p k hp hk
    (fun σ => degFl (pLie (N := N) j (k - 1) σ * Q)) (Sum.inl τ)
  have hb : degFl (bracket j φ p k τ * Q) =
      (k : ℝ) * ∑ σ, co φ p k (Sum.inl τ) σ * degFl (pLie (N := N) j (k - 1) σ * Q) := by
    unfold bracket
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, Finset.sum_mul, DeltaTermLin.degFl_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, hlie]
  rw [hb, hco]
  simp only [deltaTerm, pLie]
  ring

end GlobalTheory.CompanionTheory.Ar.Num

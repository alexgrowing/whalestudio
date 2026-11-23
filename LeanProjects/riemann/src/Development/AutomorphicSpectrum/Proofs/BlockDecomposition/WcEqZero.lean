import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm

noncomputable section

open MeasureTheory GroundTheory.LocalField Ad3 Ad3.K
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WcB

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def gaussI (χ : AddChar F Circle) (μ : Measure E) (Φ : E → ℂ) (κ : F) (ξ : E) : ℂ :=
  ∫ u, (χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u ∂μ

def wS (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ)
    (g : GL (Fin 2) F) (t : Eˣ) : ℂ :=
  ((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    GL2LocalData.rW χ σ μ lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
      (fun x => Φ (x * (t : E))) 1

theorem Wc_eq_wS (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ)
    (g : GL (Fin 2) F) (h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) :
    GL2LocalData.Wc χ σ μ lam c Φ g = wS χ σ μ lam c Φ g h.choose := by
  unfold GL2LocalData.Wc wS
  rw [dif_pos h]

theorem Wc_eq_zero (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ)
    (g : GL (Fin 2) F) (h : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) :
    GL2LocalData.Wc χ σ μ lam c Φ g = 0 := by
  unfold GL2LocalData.Wc
  rw [dif_neg h]

end GlobalTheory.CompanionTheory.WcB

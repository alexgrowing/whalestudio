import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.PhaseReal.psi_trace_single : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  intro D ψ hψ θ hθ τ t hfin hsupp
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ T = psiInf D.host.F ψ (fstA D.host.F T) := by
    unfold psiInf
    congr 1
  have h2 := hψ.2.2 θ hθ (fstA D.host.F T)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) :=
    fun ρ => GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
  have h4 : ∑ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ τ (infPart D t)).re : ℝ) : ℂ) := by
    simp only [h3]
    refine Finset.sum_eq_single τ (fun ρ _ hρ => ?_) (fun h => absurd (Finset.mem_univ τ) h)
    rw [hsupp ρ hρ]
    simp
  rw [h1, h2, h4]
  congr 1
  have h5 : ((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re = -(4 * Real.pi) * (θ τ (infPart D t)).re := by
    have : (-(4 * Real.pi : ℂ)) = ((-(4 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [h5]
  push_cast
  ring

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableSubspaceExponentFunctional
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_stable_subspace_exponent_functional : GlobalTheory.Published.Langlands.Induced → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ H₀ T : Matrix (Fin n) (Fin n) ℂ, H₀ ∈ lieSet ε → T ∈ lieSet ε → (∀ x : ℝ, IsSplit ε I.W (Pi.single ⟨0, h⟩ x) (expG ε H₀ x)) → (∀ θ : ℝ, expG ε T θ ∈ KG ε ⊓ I.M ∧ ∀ m ∈ I.M, expG ε T θ * m = m * expG ε T θ) → ∀ Y : Submodule ℂ I.H, Y ≤ kFinVec ε I.ρ → Y ≠ ⊥ → IsKStableOn ε I.ρ Y → ∃ (ℓ : I.H →ₗ[ℂ] ℂ) (γ : ℂ), (∃ y ∈ Y, ℓ y ≠ 0) ∧ (∀ X ∈ lieSet ε, (∀ t, expG ε X t ∈ flagN ε I.W) → ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ X w) = 0) ∧ (∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ H₀ w) = (I.s ⟨0, h⟩ + n - 1) * ℓ w) ∧ ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ T w) = γ * ℓ w := by
  first | exact @GlobalTheory.IndFunctional.functional | exact GlobalTheory.IndFunctional.functional | (intros; apply GlobalTheory.IndFunctional.functional <;> assumption)

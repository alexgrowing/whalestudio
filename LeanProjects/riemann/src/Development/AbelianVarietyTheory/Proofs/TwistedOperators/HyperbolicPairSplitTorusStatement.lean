import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus
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
theorem _root_.GlobalTheory.T.hyperbolic_pair_split_torus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ ∈ lieSet ε ∧ (∀ x : ℝ, IsSplit ε W (Pi.single ⟨0, h⟩ x) (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x)) ∧ P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ ∈ lieSet ε ∧ ∀ θ : ℝ, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ ∈ KG ε ⊓ leviOne ε W ∧ ∀ m ∈ leviOne ε W, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ * m = m * expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ := by
  first | exact @GlobalTheory.SplitTorus.split_torus_circle | exact GlobalTheory.SplitTorus.split_torus_circle | (intros; apply GlobalTheory.SplitTorus.split_torus_circle <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesIntertwining
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_in_stages_intertwining : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  first | exact @GlobalTheory.RealInd.Stages.stageFun_law | exact GlobalTheory.RealInd.Stages.stageFun_law | (intros; apply GlobalTheory.RealInd.Stages.stageFun_law <;> assumption)

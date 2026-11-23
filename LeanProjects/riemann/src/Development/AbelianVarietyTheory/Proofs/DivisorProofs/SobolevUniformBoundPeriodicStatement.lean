import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_uniform_bound_periodic : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  first | exact @GlobalTheory.SobClass.sob_class | exact GlobalTheory.SobClass.sob_class | (intros; apply GlobalTheory.SobClass.sob_class <;> assumption)

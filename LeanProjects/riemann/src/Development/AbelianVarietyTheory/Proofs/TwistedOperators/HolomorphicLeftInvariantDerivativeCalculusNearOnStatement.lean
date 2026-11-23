import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicLeftInvariantDerivativeCalculusNearOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one : ∀ (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Matrix (Fin n) (Fin n) ℂ → B), AnalyticAt ℂ f 1 → (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧ (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧ ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1] Rz Z (fun z => fderiv ℂ f z (Y * z)) := by
  first | exact @GlobalTheory.SphJetCalc.leftInvariant_calculus | exact GlobalTheory.SphJetCalc.leftInvariant_calculus | (intros; apply GlobalTheory.SphJetCalc.leftInvariant_calculus <;> assumption)

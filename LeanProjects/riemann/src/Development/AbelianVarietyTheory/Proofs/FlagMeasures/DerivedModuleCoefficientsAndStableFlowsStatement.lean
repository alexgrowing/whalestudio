import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedModule_coefficients_and_stable_flows : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (w : List (Fin n × Fin n)) (v : V) (y : H), ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) g = ⟪y, σ g (ew E w v : V)⟫_ℂ) ∧ (∀ W : Submodule ℂ V, FiniteDimensional ℂ W → (KStable ε E W ↔ IsKStableOn ε σ (W.map V.subtype))) ∧ ∀ (μ : Fin n → ℝ) (v : V), IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
  first | exact @GlobalTheory.Jet.Coef.coef_flow | exact GlobalTheory.Jet.Coef.coef_flow | (intros; apply GlobalTheory.Jet.Coef.coef_flow <;> assumption)

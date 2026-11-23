import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_K_type_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → lowKSub ε lam σ ≤ V → ∀ x ∈ lowKSub ε lam σ, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → AnalyticOnNhd ℝ (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) Set.univ := by
  first | exact @GlobalTheory.Jet.Anal.lowK_analytic | exact GlobalTheory.Jet.Anal.lowK_analytic | (intros; apply GlobalTheory.Jet.Anal.lowK_analytic <;> assumption)

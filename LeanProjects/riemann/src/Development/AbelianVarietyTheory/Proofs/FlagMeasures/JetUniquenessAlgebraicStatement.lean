import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JetUniquenessAlgebraic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_uniqueness_algebraic : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (E' : Fin n → Fin n → Module.End ℂ V') (ι : V →ₗ[ℂ] V') (ev : V' →ₗ[ℂ] V), GlRel E' → (∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) → (∀ y, ev y ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ y, ev (E' c d y) = E c d (ev y)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E' a b (ι (at1 G a b)) = 0) → (∀ x ∈ kSpan ε E u, ev (ι x) = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ kSpan ε E u, ev (ew E' w (ι x)) = 0 := by
  first | exact @GlobalTheory.Jet.UniqAlg.uniqAlg | exact GlobalTheory.Jet.UniqAlg.uniqAlg | (intros; apply GlobalTheory.Jet.UniqAlg.uniqAlg <;> assumption)

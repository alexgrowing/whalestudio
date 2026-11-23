import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordLaplacianPowerBound
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_word_laplacian_power_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → AlgEst → ClsFacts → IbpSob →
    ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f : Mat n → V, Sob μ f →
      ‖cls μ (Rw w f)‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound | exact GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound <;> assumption)

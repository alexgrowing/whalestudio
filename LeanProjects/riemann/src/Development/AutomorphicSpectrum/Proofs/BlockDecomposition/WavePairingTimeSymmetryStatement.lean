import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WavePairingTimeSymmetry
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_pairing_time_symmetry : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.wave_symm | exact GlobalTheory.CompanionTheory.WaveMult.wave_symm | (intros; apply GlobalTheory.CompanionTheory.WaveMult.wave_symm <;> assumption)

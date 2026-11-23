import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousArchimedeanSmoothing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedean_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ), Ker ν β → Continuous f → Continuous (sm ν β f) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker | exact GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker | (intros; apply GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker <;> assumption)

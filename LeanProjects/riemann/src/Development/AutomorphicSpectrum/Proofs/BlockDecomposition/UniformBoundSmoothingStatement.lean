import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSmoothing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ), Ker ν β → (∀ i, Continuous (f i)) →
  UBnd f m → UBnd (fun i => sm ν β (f i)) m := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uBnd_sm | exact GlobalTheory.CompanionTheory.Conc.uBnd_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uBnd_sm <;> assumption)

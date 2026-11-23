import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSet
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_siegel_set : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | exact GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | (intros; apply GlobalTheory.CompanionTheory.Conc.TailU.tail_unif <;> assumption)

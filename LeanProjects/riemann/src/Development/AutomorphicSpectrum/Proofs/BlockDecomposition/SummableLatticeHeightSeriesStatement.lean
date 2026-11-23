import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableLatticeHeightSeries
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_lattice_height_series : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (w : InfinitePlace K) (M : ℕ), 0 < M → Summable (fun p : K × K × K => if (∃ a : 𝓞 K, (a : K) = (M : K) * p.1) ∧ (∃ a : 𝓞 K, (a : K) = (M : K) * p.2.1) ∧ (∃ a : 𝓞 K, (a : K) = (M : K) * p.2.2) then ((1 + w p.1 + w p.2.1) ^ 5 * (1 + w p.2.2) ^ 3)⁻¹ else (0 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.KMajSum.summable_lattice_majorant | exact GlobalTheory.CompanionTheory.KMajSum.summable_lattice_majorant | (intros; apply GlobalTheory.CompanionTheory.KMajSum.summable_lattice_majorant <;> assumption)

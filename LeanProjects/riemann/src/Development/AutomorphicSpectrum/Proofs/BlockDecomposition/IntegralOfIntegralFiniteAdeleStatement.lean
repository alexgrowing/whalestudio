import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfIntegralFiniteAdele
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_integral_finite_adele : ∀ (K : Type) [Field K] [NumberField K] (x : K), algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ integralFiniteAdeles (𝓞 K) K → ∃ a : 𝓞 K, (a : K) = x := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles | exact GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles | (intros; apply GlobalTheory.CompanionTheory.Adelic.exists_integer_of_mem_integralFiniteAdeles <;> assumption)

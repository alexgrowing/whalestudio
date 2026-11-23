import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWBorelMul
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_W_mul_eq_norm_W_dg_of_diag : ∀ (K : Type) [Field K] [NumberField K] (V : Submodule ℂ (Ad3.K.G3K K → ℂ)), Ad3.K.WhAK V → ∀ W ∈ V, ∀ β ∈ (Reduction.adelicBorel : Subgroup (Ad3.K.G3K K)), ∀ t1 t2 t3 : (𝔸[K])ˣ, (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 0 0 = t1 → (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 1 1 = t2 → (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 2 2 = t3 → ∀ k : Ad3.K.G3K K, ‖W (β * k)‖ = ‖W (Ad3.dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 * k)‖ := by
  first | exact @GlobalTheory.CompanionTheory.MajIwaK.norm_W_borel_mul | exact GlobalTheory.CompanionTheory.MajIwaK.norm_W_borel_mul | (intros; apply GlobalTheory.CompanionTheory.MajIwaK.norm_W_borel_mul <;> assumption)

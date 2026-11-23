import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNormDiagonalReduction
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_norm_diagonal_reduction : ∀ (V : Submodule ℂ (G3 → ℂ)), WhA V → ∀ W ∈ V, ∀ β ∈ (Reduction.adelicBorel : Subgroup G3), ∀ t1 t2 t3 : (𝔸[ℚ])ˣ, (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 0 0 = t1 → (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 1 1 = t2 → (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 2 2 = t3 → ∀ k : G3, ‖W (β * k)‖ = ‖W (dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 * k)‖ := by
  first | exact @GlobalTheory.CompanionTheory.MajIwa.norm_W_borel_mul | exact GlobalTheory.CompanionTheory.MajIwa.norm_W_borel_mul | (intros; apply GlobalTheory.CompanionTheory.MajIwa.norm_W_borel_mul <;> assumption)

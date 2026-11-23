import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicNormRatVectorBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_norm_rat_vector_bound : ∀ M : ℕ, 0 < M → ∀ z : Fin 3 → ℚ, (∀ i, ∃ k : ℤ, (M : ℚ) * z i = k) → Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) ≤ M * ∑ i, |((z i : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le | exact GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le | (intros; apply GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le <;> assumption)

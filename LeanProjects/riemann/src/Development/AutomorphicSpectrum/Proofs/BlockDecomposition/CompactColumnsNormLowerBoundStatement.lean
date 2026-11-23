import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactColumnsNormLowerBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_columns_norm_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdelicGLn.AdelicGL K 3)), IsCompact C → ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ C, ∀ j : Fin 3, Reduction.HasFiniteContent (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) ∧ ε ≤ Reduction.adelicNorm (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) := by
  first | exact @GlobalTheory.CompanionTheory.AdelicColumnK.column_bound | exact GlobalTheory.CompanionTheory.AdelicColumnK.column_bound | (intros; apply GlobalTheory.CompanionTheory.AdelicColumnK.column_bound <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicColumnNormLower
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adelic_column_norm_lower : ∀ (C : Set (AdelicGLn.AdelicGL ℚ 3)), IsCompact C → ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ C, ∀ j : Fin 3, Reduction.HasFiniteContent (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) i j) ∧ ε ≤ Reduction.adelicNorm (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) i j) := by
  first | exact @GlobalTheory.CompanionTheory.AdelicColumn.column_bound | exact GlobalTheory.CompanionTheory.AdelicColumn.column_bound | (intros; apply GlobalTheory.CompanionTheory.AdelicColumn.column_bound <;> assumption)

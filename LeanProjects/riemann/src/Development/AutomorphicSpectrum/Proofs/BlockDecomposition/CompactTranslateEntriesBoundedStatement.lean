import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBounded
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_translate_entries_bounded : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (h₀ : GL (Fin 2) F), ∃ M : ℝ, 0 < M ∧ ∀ k ∈ GLnLocal.integralGL F 2, (∀ i j, (modulus ((k * h₀).val i j) : ℝ) ≤ M) ∧ modulus ((k * h₀).val).det = modulus (h₀.val).det := by
  first | exact @GlobalTheory.CompanionTheory.KHBound.entries_det_bound | exact GlobalTheory.CompanionTheory.KHBound.entries_det_bound | (intros; apply GlobalTheory.CompanionTheory.KHBound.entries_det_bound <;> assumption)

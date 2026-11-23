import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtension
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
theorem _root_.GlobalTheory.T.weil_whittaker_support_quadratic_extension : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∃ C : ℝ, 0 < C ∧ ∀ κ : F, ∃ M : AddSubgroup E, IsCompact (M : Set E) ∧ IsOpen (M : Set E) ∧ (∀ r ∈ M, ∀ u, Φ (u + r) = Φ u) ∧ (∀ r ∈ M, χ (κ * Algebra.norm F r) = 1) ∧ ∀ x : E, (∀ r ∈ M, χ (Algebra.trace F E (x * r)) = 1) → (modulus x : ℝ) ≤ C * max 1 (modulus κ : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.LatticeChoice.exists_lattice_adapted | exact GlobalTheory.CompanionTheory.LatticeChoice.exists_lattice_adapted | (intros; apply GlobalTheory.CompanionTheory.LatticeChoice.exists_lattice_adapted <;> assumption)

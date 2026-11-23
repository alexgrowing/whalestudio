import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_galois_place_degree_two : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal) (σ : Kv K w ≃ₐ[Qv v] Kv K w), σ ≠ AlgEquiv.refl → Module.finrank (Qv v) (Kv K w) = 2 := by
  first | exact @GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl | exact GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl | (intros; apply GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl <;> assumption)

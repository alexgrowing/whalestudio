import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSmoothVector
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_smooth_vector : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ (χ : AddChar F Circle), Continuous χ → ∀ (σ : E ≃ₐ[F] E) (lam : ℂ) (c : Eˣ →* ℂˣ) (n : ℕ) (a : Fin n → ℂ) (Ψ : Fin n → E → ℂ), (∀ j, Continuous (Ψ j)) → (∀ j, HasCompactSupport (Ψ j)) → ∀ g : GL (Fin 2) F, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (fun z => ∑ j, a j * Ψ j z) g = ∑ j, a j * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (Ψ j) g := by
  first | exact @GlobalTheory.CompanionTheory.WinertLin.Wc_sum | exact GlobalTheory.CompanionTheory.WinertLin.Wc_sum | (intros; apply GlobalTheory.CompanionTheory.WinertLin.Wc_sum <;> assumption)

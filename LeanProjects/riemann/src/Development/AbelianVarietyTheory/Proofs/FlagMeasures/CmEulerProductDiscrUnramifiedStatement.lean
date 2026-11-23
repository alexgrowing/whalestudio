import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_euler_product_discr_unramified : ∀ (I : AutInst) (M : ℕ), 2 ≤ M → HasProd (fun u : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) => 1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ M)⁻¹) (Formalism.HermitianLatticesTheory.lValEta I.E M)⁻¹ ∧ |(discr I.F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ I.f ∧ ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace I.F I.E u := by
  first | exact @GlobalTheory.DensityEuler.euler_product_discr_unramified | exact GlobalTheory.DensityEuler.euler_product_discr_unramified | (intros; apply GlobalTheory.DensityEuler.euler_product_discr_unramified <;> assumption)

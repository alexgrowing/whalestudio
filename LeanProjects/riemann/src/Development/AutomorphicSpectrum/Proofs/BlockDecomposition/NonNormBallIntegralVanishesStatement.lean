import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormBallIntegralVanishes
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_norm_ball_integral_vanishes : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
  (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F := by
  first | exact @GlobalTheory.CompanionTheory.NormFib.map_norm_add_translate_eq_smul | exact GlobalTheory.CompanionTheory.NormFib.map_norm_add_translate_eq_smul | (intros; apply GlobalTheory.CompanionTheory.NormFib.map_norm_add_translate_eq_smul <;> assumption)

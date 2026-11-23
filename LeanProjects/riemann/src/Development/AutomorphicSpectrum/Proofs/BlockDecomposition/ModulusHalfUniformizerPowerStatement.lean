import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfUniformizerPower
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_half_uniformizer_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ), mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := by
  first | exact @GlobalTheory.CompanionTheory.WS.mp_uniformizer_zpow_half | exact GlobalTheory.CompanionTheory.WS.mp_uniformizer_zpow_half | (intros; apply GlobalTheory.CompanionTheory.WS.mp_uniformizer_zpow_half <;> assumption)

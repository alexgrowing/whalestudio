import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerIntegralLatticeTorusFormula
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
theorem _root_.GlobalTheory.T.inner_integral_lattice_torus_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := by
  first | exact @GlobalTheory.CompanionTheory.WS.InnTorus.inner_integral_standard_lattice_torus | exact GlobalTheory.CompanionTheory.WS.InnTorus.inner_integral_standard_lattice_torus | (intros; apply GlobalTheory.CompanionTheory.WS.InnTorus.inner_integral_standard_lattice_torus <;> assumption)

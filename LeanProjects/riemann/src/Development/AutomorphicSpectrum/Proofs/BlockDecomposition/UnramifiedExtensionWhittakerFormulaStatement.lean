import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionWhittakerFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantSeparatingSubalgebraStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_whittaker_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x = ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  first | exact @GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp.sbc_decomp | exact GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp.sbc_decomp | (intros; apply GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp.sbc_decomp <;> assumption)

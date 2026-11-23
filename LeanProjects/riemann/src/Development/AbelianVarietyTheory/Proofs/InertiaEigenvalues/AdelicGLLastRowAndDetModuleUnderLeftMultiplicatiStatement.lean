import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLLastRow_and_detModule_under_left_multiplication : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  first | (exact @GlobalTheory.UnfoldRows.rows_main) | (exact GlobalTheory.UnfoldRows.rows_main) | (intros; apply GlobalTheory.UnfoldRows.rows_main  <;> assumption)

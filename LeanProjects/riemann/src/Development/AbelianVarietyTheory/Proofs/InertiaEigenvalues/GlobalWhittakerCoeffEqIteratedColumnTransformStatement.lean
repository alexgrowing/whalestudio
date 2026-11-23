import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  first | exact @GlobalTheory.WhitCols.whit_eq_colWhit | exact GlobalTheory.WhitCols.whit_eq_colWhit | (intros; apply GlobalTheory.WhitCols.whit_eq_colWhit; all_goals assumption)

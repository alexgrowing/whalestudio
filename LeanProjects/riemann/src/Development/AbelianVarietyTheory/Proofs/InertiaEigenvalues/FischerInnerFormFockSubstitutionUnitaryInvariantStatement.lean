import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  first | exact @GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | exact GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | (intros; apply GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary <;> assumption)

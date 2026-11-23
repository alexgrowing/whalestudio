import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_projector_forms_idempotent : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  first | exact @GlobalTheory.GoodSS.Idem.goodProjW_idem | exact GlobalTheory.GoodSS.Idem.goodProjW_idem | (intros; apply GlobalTheory.GoodSS.Idem.goodProjW_idem <;> assumption)

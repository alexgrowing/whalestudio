import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra := by
  first | exact @GlobalTheory.JSW.invT_mem_mspanR_contra | exact GlobalTheory.JSW.invT_mem_mspanR_contra | (intros; apply GlobalTheory.JSW.invT_mem_mspanR_contra <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothKernelRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_smooth_kernel_representation : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : GlobalTheory.CuspRep.Lie E a → ℂ), GlobalTheory.JSW.IsTestInf f → GlobalTheory.JSW.IsRapidInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) ∧ ∀ F : GlobalTheory.CuspRep.GA E a → ℂ, GlobalTheory.JSW.smoothInf f F = GlobalTheory.JSW.kerInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) F := by
  first | exact @GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf | exact GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf | (intros; apply GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf <;> assumption)

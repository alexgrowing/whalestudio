import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicSliceSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_slice_smooth : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  first | exact @GlobalTheory.VacLine.slice_schA | exact GlobalTheory.VacLine.slice_schA | (intros; apply GlobalTheory.VacLine.slice_schA <;> assumption)

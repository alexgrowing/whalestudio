import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilationDifferenceMemSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dilation_difference_mem_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ → ∀ a : kˣ, (fun x => Φ (a * x) - ((GlobalTheory.SmGL.absPow k 1 a : ℂˣ) : ℂ)⁻¹ * Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k := by
  first | exact @GlobalTheory.PrinTwo.dilate_sub_mem_elemSpan_target | exact GlobalTheory.PrinTwo.dilate_sub_mem_elemSpan_target | (intros; apply GlobalTheory.PrinTwo.dilate_sub_mem_elemSpan_target <;> assumption)

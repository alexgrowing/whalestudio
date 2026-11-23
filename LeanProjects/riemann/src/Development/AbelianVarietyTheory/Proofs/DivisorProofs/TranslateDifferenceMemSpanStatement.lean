import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDifferenceMemSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_difference_mem_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsEvRad Φ → ∀ y : k, (fun x => Φ (x + y) - Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k := by
  first | exact @GlobalTheory.PrinTwo.DiffTr.diff_mem_elemSpan | exact GlobalTheory.PrinTwo.DiffTr.diff_mem_elemSpan | (intros; apply GlobalTheory.PrinTwo.DiffTr.diff_mem_elemSpan <;> assumption)

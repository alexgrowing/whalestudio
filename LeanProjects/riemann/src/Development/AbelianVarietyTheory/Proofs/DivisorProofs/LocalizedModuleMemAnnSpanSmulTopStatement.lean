import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTop
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem : ∀ (D : Type) [CommRing D] (S : Submonoid D) (x : D) (N : Type 1) [AddCommGroup N] [Module D N], (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) → ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 → n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} • (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  first | exact @GlobalTheory.localizedModule_mem_annSpan_smul_top | exact GlobalTheory.localizedModule_mem_annSpan_smul_top | (intros; apply GlobalTheory.localizedModule_mem_annSpan_smul_top <;> assumption)

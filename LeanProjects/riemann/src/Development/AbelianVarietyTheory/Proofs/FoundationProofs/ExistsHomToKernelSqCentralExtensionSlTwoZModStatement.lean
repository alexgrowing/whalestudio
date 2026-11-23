import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  first | exact @GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | exact GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | (intros; apply GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 <;> assumption)

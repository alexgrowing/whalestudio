import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_additive_fn_pDivGroup : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (b : G.A 1), cobOne R (G.A 1) b = 0 → ∃ B : G.funs, B.1 1 = b ∧ ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  first | exact @GlobalTheory.PDivGroup.exists_funs_transl_eq_add | exact GlobalTheory.PDivGroup.exists_funs_transl_eq_add | (intros; apply GlobalTheory.PDivGroup.exists_funs_transl_eq_add <;> assumption)

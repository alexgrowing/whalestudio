import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformSkewMemUnitaryGroup
import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option autoImplicit false
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup : ∀ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E),
    J.det ≠ 0 → Formalism.UG.cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyUnitary.cayley_mem_UJ | exact GlobalTheory.CayleyUnitary.cayley_mem_UJ | (intros; apply GlobalTheory.CayleyUnitary.cayley_mem_UJ <;> assumption)

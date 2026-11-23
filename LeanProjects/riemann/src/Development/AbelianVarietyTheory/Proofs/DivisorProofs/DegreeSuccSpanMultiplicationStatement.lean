import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSuccSpanMultiplication
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_succ_span_multiplication : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (k : ℕ),
    GlobalTheory.KFixIrr.degLE ι P Q R S (k + 1) ≤ GlobalTheory.KFixIrr.degLE ι P Q R S k ⊔ Submodule.span ℂ
      {T' | ∃ (w : ι) (l : Formalism.BasicNotions.TH.Ln P Q R S), ∃ T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w
          (LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S)) T} := by
  first | exact @GlobalTheory.KFixIrr.DegSucc.degLE_succ_le | exact GlobalTheory.KFixIrr.DegSucc.degLE_succ_le | (intros; apply GlobalTheory.KFixIrr.DegSucc.degLE_succ_le <;> assumption)

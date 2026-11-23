import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFixedDegreeFiltrationStepUp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_fixed_degree_filtration_step_up : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (c : ι → ℚ) (m : ℕ)
    (T₀ T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T₀ ≠ 0 →
    T₀ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
    T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 2) →
    T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 1) ⊔ Submodule.span ℂ {T' | ∃ (w : ι) (Z : Formalism.BasicNotions.TH.Mat R S),
      ∃ T₁ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T₁} := by
  first | exact @GlobalTheory.KFixIrr.evenStep_tens | exact GlobalTheory.KFixIrr.evenStep_tens | (intros; apply GlobalTheory.KFixIrr.evenStep_tens <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonalLagrangian_invariant_form : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ], ∃ l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (κ ⊕ κ) ∧ (∀ (x y : κ → AF F), ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧ ∃ φ ∈ schA F (κ ⊕ κ), l φ ≠ 0 := by
  first | exact @GlobalTheory.diagLagrangian_form | exact GlobalTheory.diagLagrangian_form | (intros; apply GlobalTheory.diagLagrangian_form <;> assumption)

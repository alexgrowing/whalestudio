import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorPreservesEquivariantRightInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_preserves_equivariantRightInvariant : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) → ∀ φ ∈ eqvM ι ρ K', levOp (rightReg ℂ G V) K K' F LinearMap.id φ ∈ eqvM ι ρ K' := by
  first | exact @GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM | exact GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM | (intros; apply GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM <;> assumption)

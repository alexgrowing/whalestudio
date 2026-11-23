import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)

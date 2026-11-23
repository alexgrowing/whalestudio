import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_induction_column_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j))
    (hm : b.1 false 1 + b.1 true 1 = m),
    Nonempty (Representation.Equiv ((parInd (g 1) (colRep f (detPair k a a' α₀ β₀) 1)).comp (glCast k hm))
      (cellMid k α₀ β₀ b.1)) := by
  first | exact @GlobalTheory.IndLineGL.MidColumn.parInd_colRep_equiv_cellMid | exact GlobalTheory.IndLineGL.MidColumn.parInd_colRep_equiv_cellMid | (intros; apply GlobalTheory.IndLineGL.MidColumn.parInd_colRep_equiv_cellMid <;> assumption)

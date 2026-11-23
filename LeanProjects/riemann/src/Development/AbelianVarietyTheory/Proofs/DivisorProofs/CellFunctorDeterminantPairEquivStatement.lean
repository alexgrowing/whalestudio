import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorDeterminantPairEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_determinant_pair_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    ∀ (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j)),
    Nonempty (Representation.Equiv ((cellFunctor f g (detPair k a a' α₀ β₀)).comp (midIncl k m))
      (parInd (g 1) (colRep f (detPair k a a' α₀ β₀) 1))) := by
  first | exact @GlobalTheory.IndLineGL.nonempty_cell_midIncl_equiv | exact GlobalTheory.IndLineGL.nonempty_cell_midIncl_equiv | (intros; apply GlobalTheory.IndLineGL.nonempty_cell_midIncl_equiv <;> assumption)

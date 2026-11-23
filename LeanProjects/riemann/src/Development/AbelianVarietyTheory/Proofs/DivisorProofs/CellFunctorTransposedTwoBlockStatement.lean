import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTransposedTwoBlock
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_transposed_two_block : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v)))), B.1 true false = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
          (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom)
        (extTensor (detRep (Fin 1) (χ₂ * absPow k (-(v : ℂ) / 2)))
          (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (1 / 2)))))) := by
  first | exact @GlobalTheory.SmGL.RowOneCell.cell_equiv | exact GlobalTheory.SmGL.RowOneCell.cell_equiv | (intros; apply GlobalTheory.SmGL.RowOneCell.cell_equiv <;> assumption)

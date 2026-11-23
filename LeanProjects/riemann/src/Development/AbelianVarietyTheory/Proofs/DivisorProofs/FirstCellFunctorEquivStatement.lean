import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCellFunctorEquiv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubSmulMemOfEquiv
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cell_functor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ), ∃ (f : ∀ i, (Σ j, Fin ((GlobalTheory.DetProdCells.cellFirst u v).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i) (g : ∀ j, (Σ i, Fin ((GlobalTheory.DetProdCells.cellFirst u v).1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j), Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)).comp (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom) (extTensor (detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2))) (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)))) := by
  first | exact @GlobalTheory.CellFirstDet.cellFirst_det_equiv | exact GlobalTheory.CellFirstDet.cellFirst_det_equiv | (intros; apply GlobalTheory.CellFirstDet.cellFirst_det_equiv <;> assumption)

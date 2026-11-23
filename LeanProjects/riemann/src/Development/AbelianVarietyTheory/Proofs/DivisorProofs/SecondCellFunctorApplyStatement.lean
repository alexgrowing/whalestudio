import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCellFunctorApply
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubSmulMemOfEquiv
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_cell_functor_apply : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (hv : 1 ≤ v) (ϖ : kˣ), ∃ (f : ∀ i, (Σ j, Fin ((GlobalTheory.DetProdCells.cellSecond u v hv).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i) (g : ∀ j, (Σ i, Fin ((GlobalTheory.DetProdCells.cellSecond u v hv).1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j), ∀ w, cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom) (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) w = (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  first | exact @GlobalTheory.DetProdCells.cellSecond_scalar | exact GlobalTheory.DetProdCells.cellSecond_scalar | (intros; apply GlobalTheory.DetProdCells.cellSecond_scalar <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetPairInducedFiltration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_pair_induced_filtration : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (d : ℕ) (h2 : 2 ≤ d) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = d) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) →
    ∃ (M : ℕ) (S : Fin (M + 1) → Submodule ℂ (Jacquet (pairInd k b hb χ) (unipRad k (place3 h2))))
      (r r' : Fin M → Fin 2),
      Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last M) = ⊤ ∧ (∀ s t, r s = r t → r' s = r' t → s = t) ∧
      ∀ t, ∀ v ∈ S t.succ, ∀ p : kˣ × kˣ,
        jac (place3 h2) (pairInd k b hb χ) (tor3 k d p) v - cellChar₂ k b χ (r t) (r' t) p • v ∈ S t.castSucc := by
  first | exact @GlobalTheory.IndJacBlock.jacquet_cells | exact GlobalTheory.IndJacBlock.jacquet_cells | (intros; apply GlobalTheory.IndJacBlock.jacquet_cells <;> assumption)

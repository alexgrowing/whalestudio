import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparable
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_span_corner_charpoly_separable : ∀ {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ} (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), AbsIrrDistinct (matRep σ) → b * a = 1 → a * b ∈ Submodule.span K (Set.range σ) → ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_mem_span_corner_separable | exact GlobalTheory.SpanRing.exists_mem_span_corner_separable | (intros; apply GlobalTheory.SpanRing.exists_mem_span_corner_separable <;> assumption)

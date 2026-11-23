import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem GlobalTheory.FullRankCoinv.fullRk_support_finite_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  intro k _ _ _ _ n d S hS hcov Ψ hΨ
  obtain ⟨⟨hlc, hcs⟩, hz⟩ := hΨ
  have hcl : IsClosed (Function.support Ψ) := by
    have h := (hlc.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hK : IsCompact (Function.support Ψ) :=
    IsCompact.of_isClosed_subset hcs hcl (subset_tsupport Ψ)
  have hU : ∀ E : GL (Fin n) k, IsOpen ((fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) := fun E =>
    hS.preimage (Continuous.matrix_mul continuous_const continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun E : GL (Fin n) k => (fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) hU
    (by
      intro Y hY
      have hr : Y.rank = n := by
        by_contra h
        exact hY (hz Y h)
      obtain ⟨E, hE⟩ := hcov Y hr
      exact Set.mem_iUnion.2 ⟨E, hE⟩)
  refine ⟨t, fun Y hY => ?_⟩
  have := ht hY
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨E, hEt, hE⟩ := this
  exact ⟨E, hEt, hE⟩

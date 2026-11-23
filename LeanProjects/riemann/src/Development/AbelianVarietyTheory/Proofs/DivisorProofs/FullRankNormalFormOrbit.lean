import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv

theorem exists_eq_normal_form_mul_of_rank_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (hnd : n ≤ d)
    (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  let σ : Fin n ⊕ Fin (d - n) ≃ Fin d :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσ : ∀ i : Fin n, ((σ (Sum.inl i) : Fin d) : ℕ) = d - n + i := fun i => by
    simp [σ]
  have hX : X0 k σ = GlobalTheory.FullRankCoinv.Y0 k n d := by
    ext i j
    simp only [X0, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]
    congr 1
    apply propext
    rw [← hσ i, eq_comm]
    exact Fin.val_inj.symm
  have hc : Y.rank = Fintype.card (Fin n) := by simpa using hY
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hc
  exact ⟨invT h, by rw [hh, hX]⟩

end GlobalTheory.FullRankCoinv

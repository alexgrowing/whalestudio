import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem muD_toReal_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    ((muD k t) E).toReal ≠ 0 := by
  intro k _ _ _ _ t E C hE hn hC hEC
  unfold muD
  rw [ENNReal.toReal_ne_zero]
  exact ⟨(hE.measure_pos _ hn).ne',
    ((MeasureTheory.measure_mono hEC).trans_lt hC.measure_lt_top).ne⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

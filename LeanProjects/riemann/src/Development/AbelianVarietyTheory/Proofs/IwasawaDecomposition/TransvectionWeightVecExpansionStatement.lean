import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_weightVec_expansion : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v → ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧ (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧ ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  first | exact @GlobalTheory.transvection_weightVec_expansion | exact GlobalTheory.transvection_weightVec_expansion | (intros; apply GlobalTheory.transvection_weightVec_expansion <;> assumption)

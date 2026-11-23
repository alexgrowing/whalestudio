import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosSmulEqOfLinearIndependentCone
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' : ∀ {L : Type} [AddCommGroup L] {m m' : ℕ} (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ), LinearIndependent ℤ δ → 0 < k → k • δ i = ∑ j, a j • γ j →
    (∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) →
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  first | exact @GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone | exact GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone | (intros; apply GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisation
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightedHomogeneous_homogenisation : ∀ {L : Type} [Field L] (Q : Subring L) (r : ℕ) (z : Fin (r + 1) → Q)
    (wt : Fin (r + 1) → ℕ), wt 0 = 1 → (z 0 : L) ≠ 0 → ∀ P : MvPolynomial (Fin r) Q,
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  first | exact @GlobalTheory.exists_weightedHomogenisation | exact GlobalTheory.exists_weightedHomogenisation | (intros; apply GlobalTheory.exists_weightedHomogenisation <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorOfGaloisRelations
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  first | (exact @GlobalTheory.ht_operator_of_galois_relations) | (exact GlobalTheory.ht_operator_of_galois_relations) | (intros; apply GlobalTheory.ht_operator_of_galois_relations  <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbour
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_vectors_neighbour : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → (∀ a ∈ P, sgO D a ∈ P) → ∀ (B : Lat D n) (x : Fin n → D.host.E), SD D B → NbD D P B x → ∃ (b x' : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), B = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b} ∧ nbr D B x = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x'} ∧ (∀ p ∈ P, p • b ∈ nbM D B x ∧ p • x' ∈ nbM D B x) ∧ ¬ IntE D (hE D b x') ∧ NbD D P B (b + x') ∧ nbM D B (b + x') = nbM D B x ∧ lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x') (b + x') = 0 ∧ Nat.Coprime m q ∧ (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧ ∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x')) = (p : D.host.E) := by
  first | exact @GlobalTheory.NbVec.exists_vectors | exact GlobalTheory.NbVec.exists_vectors | (intros; apply GlobalTheory.NbVec.exists_vectors <;> assumption)

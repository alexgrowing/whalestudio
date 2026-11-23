import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOpenHopfOrder
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilocal_conjugate_same_charpoly : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  first | (exact @GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (exact GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (intros; apply GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable <;> assumption)

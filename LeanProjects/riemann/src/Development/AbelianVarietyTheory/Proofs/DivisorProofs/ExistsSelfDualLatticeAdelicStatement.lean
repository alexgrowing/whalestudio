import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeAdelic
import Mathlib
import Formalism.SatakeDualWeyl.Statement
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_lattice_adelic : ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (σ : A →+* A), (∀ a, σ (σ a) = a) →
    ∀ R : Subring A, IsCompact (R : Set A) → IsOpen (R : Set A) → (∀ a ∈ R, σ a ∈ R) → (∀ a : A, ∃ N : ℕ, N ≠ 0 ∧ (N : A) * a ∈ R) →
    (∀ N : ℕ, N ≠ 0 → IsUnit (N : A)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∃ L : Submodule R (Fin n → A), L.FG ∧ IsOpen (L : Set (Fin n → A)) ∧ IsCompact (L : Set (Fin n → A)) ∧
      (∀ u ∈ L, ∀ v ∈ L, Formalism.UG.hform σ J u v ∈ R) ∧ (∀ u ∈ L, ∃ b ∈ R, Formalism.UG.hform σ J u u = b + σ b) ∧
      ∀ x : Fin n → A, Formalism.UG.hform σ J x x = 0 → (∀ v ∈ L, Formalism.UG.hform σ J x v ∈ R) → x ∈ L := by
  first | exact @GlobalTheory.MaxEvenLat.exists_maximal_even_lattice | exact GlobalTheory.MaxEvenLat.exists_maximal_even_lattice | (intros; apply GlobalTheory.MaxEvenLat.exists_maximal_even_lattice <;> assumption)

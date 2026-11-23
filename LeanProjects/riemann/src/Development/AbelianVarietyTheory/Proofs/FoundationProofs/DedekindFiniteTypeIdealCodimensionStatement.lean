import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_finiteType_ideal_codimension : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧ (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ → Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) → I = J) := by
  first | exact @GlobalTheory.DedekindCodim.dedekind_finiteType_codim | exact GlobalTheory.DedekindCodim.dedekind_finiteType_codim | (intros; apply GlobalTheory.DedekindCodim.dedekind_finiteType_codim <;> assumption)

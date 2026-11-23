import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Formalism.LocalToGlobal.Divisibility.DefGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_symmetric_unipotent_pattern : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) → ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) → ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  first | exact @GlobalTheory.SymResCount.conj_pat_onto | exact GlobalTheory.SymResCount.conj_pat_onto | (intros; apply GlobalTheory.SymResCount.conj_pat_onto <;> assumption)

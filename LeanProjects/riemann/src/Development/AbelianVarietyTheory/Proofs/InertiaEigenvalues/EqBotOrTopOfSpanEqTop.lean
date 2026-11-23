import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantAll
open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff

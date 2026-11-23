import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGL
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_generated_commuting_blockGL : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ) (h : ∀ c : Set.range b, (block b c).card = d c), ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi F b, (∀ (c : Set.range b) (g : GL (Fin (d c)) F), (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧ (⨆ c, (f c).range) = ⊤ ∧ ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F), Commute (f c x) (f c' y) := by
  first | exact @GlobalTheory.Parabolic.LeviGen.levi_generated | exact GlobalTheory.Parabolic.LeviGen.levi_generated | (intros; apply GlobalTheory.Parabolic.LeviGen.levi_generated <;> assumption)
